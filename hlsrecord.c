#if 0
gcc -g -O0 -o ~/bin/hlsrecord -fwrapv hlsrecord.c -lm -lrt `curl-config --cflags --libs`
exit
#endif

#define _FILE_OFFSET_BITS 64
#define _GNU_SOURCE
#include <curl/curl.h>
#include <err.h>
#include <errno.h>
#include <math.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/timerfd.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#define ERR_OPTION 3
#define ERR_M3U 4
#define ERR_CURL 5
#define ERR_MEMORY 6
#define ERR_URL 7
#define ERR_FILE 8
#define ERR_OTHERS 9
#define ERR_LIMIT 10

#define M3ULINEMAX 5000

static time_t starttime,endtime;
static uint64_t maxtotal=0xFFFFFFFFFFFFFFFFULL;
static uint16_t maxsegments=0xFFFF;
static char*baseurl;
static char*urlprefix;
static struct curl_slist*reqheaders;
static FILE*log_out;
static FILE*video_out;
static int base_retry_time,max_retry_time,max_retry_count,retry_count;
static char nodownload;
static struct timespec timing[26];
static char commercial_skip,want_range,want_progress;

static CURL*m3ucurl;
static CURL*tscurl;
static time_t begintime;

static char m3uline[M3ULINEMAX+2];
static int m3ulinepos;
static uint64_t oldseqnumber,firstseqnumber,seqnumber,lastseqnumber;
static char ended=0;
static char ended_program=0;
static char criteria=1;
static struct timespec targetduration={.tv_sec=5,.tv_nsec=0};
static struct timespec segtime,totalsegtime,lastsegtime;
static uint64_t video_total=0;
static time_t first_time,last_time;
static uint64_t content_length,received_length;

static char cueout_on;
static struct timespec cueout_time;

static uint16_t nsegments;
static FILE*segments_file;
static char*segments_str;
static size_t segments_size;

static int timer1,timer_flag;
static struct timespec request_time;

static const struct timespec zerotime={};

static void show_progress(const char*id) {
  // The "id" should consists of two characters
  static uint8_t spin=0;
  printf("\rhlsrecord: %c %s%c%c%c%c seq=%020llu vt=%020llu rec=%020llu nseg=%05u retry=%010d","|/-\\"[spin++&3],id
   ,criteria?'^':'_',cueout_on?'C':'_',ended?'E':'_',ended_program?'P':'_'
   ,(long long)seqnumber,(long long)video_total,(long long)received_length,nsegments,retry_count);
}

static void convert_url(const char*base,const char*rel,FILE*out) {
  char nofile=0;
  int n;
  const char*colon;
  const char*query;
  const char*slash;
  const char*frag;
  const char*p;
  if(!rel) errx(ERR_URL,"URL is missing");
  for(n=0;rel[n] && ((rel[n]>='A' && rel[n]<='Z') || (rel[n]>='a' && rel[n]<='z') || rel[n]=='-' || rel[n]=='_' || (rel[n]>='0' && rel[n]<='9'));n++);
  if(rel[n]==':') {
    for(n=0;rel[n]!=':';n++) {
      if(rel[n]>='A' && rel[n]<='Z') fputc(rel[n]+'a'-'A',out); else fputc(rel[n],out);
    }
    fputs(rel+n,out);
    return;
  }
  if(!base) errx(ERR_URL,"Cannot convert relative URL to absolute due to unspecified base URL");
  colon=strchr(base,':');
  // This program does not use URLs without "://"
  if(!colon || colon[1]!='/' || colon[2]!='/') errx(ERR_URL,"Invalid base URL \"%s\"",base);
  if(!*rel) {
    fputs(base,out);
    return;
  }
  colon+=3;
  fwrite(base,1,colon-base,out);
  base=colon;
  if(rel[0]!='/' || rel[1]!='/') {
    p=strchrnul(base,'/');
    fwrite(base,1,p-base,out);
    base=p;
  }
  if(*rel=='/') {
    fputs(rel+(rel[1]=='/'?2:0),out);
    return;
  } else {
    fputc('/',out);
    if(*base) ++base;
  }
  frag=strchrnul(base,'#');
  query=strchrnul(base,'?');
  if(query>frag) query=frag;
  for(slash=query;slash>base && *slash!='/';--slash);
  repeat:
  if(*rel=='.') {
    if(rel[1]=='/' || rel[1]=='?' || rel[1]=='#' || !rel[1]) {
      rel+=(rel[1]=='/'?2:1);
      nofile=1;
      goto repeat;
    } else if(rel[1]=='.' && (rel[2]=='/' || rel[2]=='?' || rel[2]=='#' || !rel[2])) {
      rel+=(rel[2]=='/'?3:2);
      nofile=1;
      if(slash>base) for(--slash;slash>base && *slash!='/';--slash);
      goto repeat;
    }
  }
  if(*rel=='?') {
    if(nofile) {
      fwrite(base,1,slash-base,out);
      if(slash>base) fputc('/',out);
    } else {
      fwrite(base,1,query-base,out);
    }
  } else if(*rel=='#') {
    fwrite(base,1,frag-base,out);
  } else if(slash!=base) {
    fwrite(base,1,slash-base,out);
    fputc('/',out);
  }
  fputs(rel,out);
}

static time_t iso8601_to_unix(const char*in) {
  struct tm tm={};
  int c,n;
  double frac=0.0;
  while(*in==' ') ++in;
  // This program supports a nonstandard extension, which is @ followed by a decimal UNIX timestamp number.
  if(*in=='@') return strtoll(in+1,0,10);
  // Date
  for(n=0;n<4 && in[n]>='0' && in[n]<='9';n++) tm.tm_year=10*tm.tm_year+in[n]-'0';
  in+=n; if(*in=='-') ++in;
  tm.tm_year-=1900;
  for(n=0;n<2 && in[n]>='0' && in[n]<='9';n++) tm.tm_mon=10*tm.tm_mon+in[n]-'0';
  in+=n; if(*in=='-') ++in;
  tm.tm_mon--;
  for(n=0;n<2 && in[n]>='0' && in[n]<='9';n++) tm.tm_mday=10*tm.tm_mday+in[n]-'0';
  in+=n;
  // Time
  if(*in=='T') {
    ++in;
    for(n=0;n<2 && in[n]>='0' && in[n]<='9';n++) tm.tm_hour=10*tm.tm_hour+in[n]-'0';
    in+=n; if(*in==':') ++in;
    for(n=0;n<2 && in[n]>='0' && in[n]<='9';n++) tm.tm_min=10*tm.tm_min+in[n]-'0';
    in+=n;
    if(*in=='.' || *in==',') {
      for(++in,n=0;in[n]>='0' && in[n]<='9';n++) frac=10*frac+in[n]-'0';
      frac*=60.0; frac/=pow(10,n);
      tm.tm_sec=frac;
    } else {
      if(*in==':') ++in;
      for(n=0;n<2 && in[n]>='0' && in[n]<='9';n++) tm.tm_sec=10*tm.tm_sec+in[n]-'0';
      in+=n;
      // This program does not use fractional seconds
      if(*in=='.' || *in==',') {
        ++in;
        while(*in>='0' && *in<='9') ++in;
      }
    }
  }
  // Zone
  while(*in==' ') ++in;
  if(*in=='Z') {
    return timegm(&tm);
  } else if(*in=='+' || *in=='-') {
    c=*in++;
    if(in[0]<'0' || in[0]>'9' || in[1]<'0' || in[1]>'9' || !in[2] || in[3]<'0' || in[3]>'9' || (in[2]==':' && !in[4])) {
      warnx("Ignoring apparently improper time zone in ISO 8601");
      return timegm(&tm);
    }
    n=(in[0]-'0')*10+(in[1]-'0'); n*=60;
    if(in[2]==':') ++in;
    n+=(in[2]-'0')*10+(in[3]-'0');
    return c=='+'?timegm(&tm)-n*60:timegm(&tm)+n*60;
  } else {
    // The time zone is unspecified (or is an unrecognized format); assume local time
    tm.tm_isdst=-1;
    return mktime(&tm);
  }
}

static uint64_t parse_file_size(const char*x) {
  uint64_t v=strtoll(x,(char**)&x,10);
  if(*x=='k' || *x=='K') v*=1024LL;
  if(*x=='m' || *x=='M') v*=1024LL*1024LL;
  if(*x=='g' || *x=='G') v*=1024LL*1024LL*1024LL;
  return v;
}

static void parse_time_interval(const char*in,struct timespec*out) {
  *out=(struct timespec){};
  while(*in>='0' && *in<='9') out->tv_sec=10*out->tv_sec+*in++-'0';
  if(*in++=='.') {
    long u=1000000000L;
    while(*in>='0' && *in<='9' && u) out->tv_nsec+=(*in++-'0')*(u/=10);
  }
}

static inline void add_timespec(const struct timespec*in,struct timespec*out) {
  uint64_t n=((uint64_t)in->tv_nsec)+((uint64_t)out->tv_nsec);
  out->tv_sec+=in->tv_sec+n/1000000000;
  out->tv_nsec=n%1000000000;
}

static inline void sub_timespec(const struct timespec*in,struct timespec*out) {
  int64_t n=((int64_t)in->tv_nsec)-((int64_t)out->tv_nsec);
  if(n<0) --out->tv_sec,n+=1000000000; else if(n>=1000000000) ++out->tv_sec,n-=1000000000;
  out->tv_sec-=in->tv_sec;
  out->tv_nsec=n;
}

static inline void half_timespec(const struct timespec*in,struct timespec*out) {
  *out=*in;
  if(out->tv_nsec>1) out->tv_nsec>>=1;
  if(in->tv_sec&1) out->tv_nsec+=500000000LL;
  out->tv_sec>>=1;
  if(out->tv_nsec>=1000000000LL) out->tv_nsec-=1000000000LL,out->tv_sec++;
}

static inline void min_timespec(const struct timespec*in,struct timespec*out) {
  if(in->tv_sec<out->tv_sec || (in->tv_sec==out->tv_sec && in->tv_nsec<out->tv_nsec)) *out=*in;
}

static inline void max_timespec(const struct timespec*in,struct timespec*out) {
  if(in->tv_sec>out->tv_sec || (in->tv_sec==out->tv_sec && in->tv_nsec>out->tv_nsec)) *out=*in;
}

static void affect_total(int64_t n) {
  if(n<=0) return;
  if(maxtotal<n) {
    if(log_out) fprintf(log_out,"ERR:LIMIT_EXCEEDED\n");
    errx(ERR_LIMIT,"Limit exceeded");
  }
  maxtotal-=n;
}

static size_t video_writer_callback(char *ptr, size_t size, size_t nmemb, void *userdata) {
  video_total+=size*nmemb;
  received_length+=size*nmemb;
  affect_total(size*nmemb);
  if(video_out) fwrite(ptr,size,nmemb,video_out);
  if(want_progress) show_progress("v+");
  return size*nmemb;
}

static size_t video_header_callback(char *ptr, size_t size, size_t nmemb, void *userdata) {
  size_t n=15;
  size*=nmemb;
  if(!content_length && size>15 && !strncasecmp(ptr,"Content-Length:",15)) {
    while(n<size && (ptr[n]==' ' || ptr[n]=='\t')) ++n;
    while(n<size && ptr[n]>='0' && ptr[n]<='9') content_length=10LL*content_length+ptr[n++]-'0';
  }
  if(want_progress) show_progress("h+");
  return size;
}

static void m3u_process_line(void) {
  if(log_out) affect_total(fprintf(log_out,"M3U:%s\n",m3uline));
  if(!memcmp(m3uline,"#EXT",4)) {
    // Command
    char*p=strchr(m3uline+4,':');
    if(p) *p++=0;
    if(!strcmp(m3uline+4,"INF") && p) {
      if(*p=='-') return; // Ignore this line if the duration is negative, since some files that do not follow the specification use this for extra TV attributes.
      parse_time_interval(p,&segtime);
      add_timespec(&segtime,&totalsegtime);
      if(log_out) affect_total(fprintf(log_out,"INF:%ld.%09ld,%ld.%09ld\n",(long)segtime.tv_sec,(long)segtime.tv_nsec,(long)totalsegtime.tv_sec,(long)totalsegtime.tv_nsec));
    } else if((starttime || endtime || !video_out) && !strcmp(m3uline+4,"-X-PROGRAM-DATE-TIME") && p) {
      time_t t=iso8601_to_unix(p);
      if(starttime && t<starttime) criteria=2;
      if(endtime && t>=endtime) criteria=0,ended_program=1;
      if(!first_time) first_time=t;
      last_time=t;
    } else if(!strcmp(m3uline+4,"-X-TARGETDURATION") && p) {
      parse_time_interval(p,&targetduration);
    } else if(!strcmp(m3uline+4,"-X-MEDIA-SEQUENCE") && p) {
      if(*p) firstseqnumber=seqnumber=strtoll(p,0,10);
    } else if(commercial_skip && !strcmp(m3uline+4,"-X-CUE-OUT-CONT")) {
      //TODO: handle the variants of #EXT-X-CUE-OUT and #EXT-X-CUE-OUT-CONT with named parameters
      cueout_on=1;
      if(p && *p) {
        struct timespec a;
        parse_time_interval(p,&a);
        if(p=strchr(p,'/')) {
          parse_time_interval(p+1,&cueout_time);
          sub_timespec(&a,&cueout_time);
        }
      } else {
        cueout_time=timing['c'-'a'];
      }
    } else if(commercial_skip && !strcmp(m3uline+4,"-X-CUE-OUT")) {
      cueout_on=1;
      if(p && *p) {
        if(!strncmp(p,"DURATION=",9)) p+=9;
        parse_time_interval(p,&cueout_time);
      } else {
        cueout_time=timing['c'-'a'];
      }
    } else if(commercial_skip && !strcmp(m3uline+4,"-X-CUE-IN")) {
      cueout_on=0;
      cueout_time=zerotime;
    } else if(!strcmp(m3uline+4,"-X-PLAYLIST-TYPE")) {
      if(p && !strcmp(p,"VOD")) ended=1;
    } else if(!strcmp(m3uline+4,"-X-GAP")) {
      criteria=0;
    } else if(!strcmp(m3uline+4,"-X-ENDLIST")) {
      ended=1;
    }
  } else if(*m3uline && *m3uline!='#' && nsegments<maxsegments && !ended_program) {
    // URL
    if(log_out) affect_total(fprintf(log_out,"SEQ:%llu,%llu,%llu,%d\n",(long long)firstseqnumber,(long long)seqnumber,(long long)lastseqnumber,criteria));
    if(cueout_on) {
      if(log_out) affect_total(fprintf(log_out,"OUT:%lld.%09ld\n",(long long)cueout_time.tv_sec,(long)cueout_time.tv_nsec));
      if(!cueout_time.tv_sec && !cueout_time.tv_nsec) cueout_on=0;
      sub_timespec(&segtime,&cueout_time);
      if(cueout_time.tv_sec<0) cueout_on=0;
      if(cueout_on) criteria=0;
    }
    if(criteria==2 && (last_time+(uint64_t)segtime.tv_sec)<starttime) criteria=0;
    lastsegtime=totalsegtime;
    sub_timespec(&segtime,&lastsegtime);
    if(seqnumber>=lastseqnumber && criteria) {
      convert_url(baseurl,m3uline,segments_file);
      fputc(0,segments_file);
      ++nsegments;
    }
    ++seqnumber;
    criteria=1;
  }
}

static size_t m3u_writer_callback(char *ptr, size_t size, size_t nmemb, void *userdata) {
  char c;
  size_t s=size*=nmemb;
  while(s--) {
    c=*ptr++;
    if(c=='\r' || !c) continue;
    if(c=='\n') {
      m3uline[m3ulinepos]=0;
      m3u_process_line();
      m3ulinepos=0;
    } else if(m3ulinepos<M3ULINEMAX) {
      m3uline[m3ulinepos++]=c;
    }
  }
  if(want_progress) show_progress("m+");
  return size;
}

static int m3u_sockopt_callback(void*clientp,curl_socket_t curlfd,curlsocktype purpose) {
  timer_flag=TFD_TIMER_ABSTIME;
  return clock_gettime(CLOCK_MONOTONIC,&request_time);
}

static void m3u_reset(void) {
  int i;
  oldseqnumber=firstseqnumber;
  if(lastseqnumber<seqnumber) lastseqnumber=seqnumber;
  firstseqnumber=seqnumber=0;
  m3ulinepos=0;
  nsegments=0;
  totalsegtime=zerotime;
  segtime=zerotime;
  cueout_time=zerotime;
  cueout_on=0;
  free(segments_str);
  segments_str=0;
  segments_size=0;
  segments_file=open_memstream(&segments_str,&segments_size);
  if(!segments_file) err(ERR_MEMORY,"Allocation failed");
  criteria=1;
}

static void do_segment(const char*url) {
  int c;
  if(log_out) affect_total(fprintf(log_out,"SEG:%llu,%s\n",(long long)(video_out?ftello(video_out):0),url));
  if(nodownload) return;
  if(urlprefix) {
    for(c=0;urlprefix[c];c++) if(url[c]!=urlprefix[c]) {
      if(log_out) fprintf(log_out,"ERR:URL_PREFIX\n");
      errx(ERR_URL,"The required URL prefix does not match");
    }
  }
  content_length=0; received_length=0;
  curl_easy_setopt(tscurl,CURLOPT_URL,url);
  if(want_range) curl_easy_setopt(tscurl,CURLOPT_RANGE,(char*)0);
  repeat:
  if(want_progress) show_progress("v-");
  while(c=curl_easy_perform(tscurl)) {
    // This program should check if the error is known to be permanent, but it currently doesn't.
    int j=base_retry_time<<retry_count;
    long q;
    struct timespec x={.tv_sec=j?random()%(j<max_retry_time?j+1:max_retry_time+1):0,.tv_nsec=j?random()%999999999:1};
    if(log_out) {
      if(video_out) fprintf(log_out,"ATO:%llu\n",(long long)ftello(video_out));
      affect_total(c==CURLE_HTTP_RETURNED_ERROR?fprintf(log_out,"ERR:HTTP:%ld\n",(curl_easy_getinfo(tscurl,CURLINFO_RESPONSE_CODE,&q),q)):fprintf(log_out,"ERR:CURL:%d\n",c));
    }
    if(retry_count++==max_retry_count) errx(ERR_CURL,"Curl error %d: %s",c,curl_easy_strerror(c));
    if(nanosleep(&x,0) && errno!=EINTR) err(ERR_OTHERS,"Error with nanosleep");
  }
  if(want_range && received_length<content_length) {
    //TODO: Scorpion range requests, which work differently from HTTP. (This also does not work with RTSP.)
    char buf[64];
    snprintf(buf,64,"%llu-%llu",(unsigned long long)received_length,(unsigned long long)(content_length-1));
    curl_easy_setopt(tscurl,CURLOPT_RANGE,buf);
    if(log_out) affect_total(fprintf(log_out,"TRY:%s\n",buf));
    if(retry_count++==max_retry_count) errx(ERR_OTHERS,"Reached maximum retry count with range request");
    goto repeat;
  }
  if(video_out) fflush(video_out);
}

static void playlist_wait(void) {
  char result[8];
  struct timespec a,t;
  struct itimerspec it={};
  if(want_progress) show_progress("t-");
  t=targetduration;
  if(seqnumber==lastseqnumber) half_timespec(&targetduration,&t);
  if(timing['p'-'a'].tv_sec || timing['p'-'a'].tv_nsec) {
    a=lastsegtime;
    sub_timespec(timing+'p'-'a',&a);
    if(timing['x'-'a'].tv_sec>0) min_timespec(timing+'x'-'a',&a);
    max_timespec(&a,&t);
    if(cueout_on && (timing['o'-'a'].tv_sec || timing['o'-'a'].tv_nsec)) {
      a=cueout_time;
      sub_timespec(timing+'o'-'a',&a);
      if(timing['x'-'a'].tv_sec>0) min_timespec(timing+'x'-'a',&a);
      max_timespec(&a,&t);
    }
  }
  if(timing['w'-'a'].tv_sec || timing['w'-'a'].tv_nsec) max_timespec(timing+'w'-'a',&t);
  if(log_out) affect_total(fprintf(log_out,"WAI:%lld.%09ld\n",(long long)t.tv_sec,(long)t.tv_nsec));
  it.it_value=t;
  if(timer_flag) add_timespec(&request_time,&it.it_value);
  timerfd_settime(timer1,timer_flag,&it,0);
  if(read(timer1,&result,8)<=0 && nanosleep(&t,0)) err(ERR_OTHERS,"Cannot sleep");
}

#define OPTSTRING "H:I:N:P:S:ce:gl:m:n:o:pqr:s:t:u:v"

static void set_option(int c,const char*a) {
  uint64_t u,v;
  char*p;
  const char*q;
  FILE*f;
  char*line=0;
  size_t line_size=0;
  switch(c) {
    case 1:
      f=fopen(a,"r");
      if(!f) err(ERR_FILE,"Cannot open options file \"%s\"",a);
      while(getline(&line,&line_size,f)>0) if(*line=='-') {
        *strchrnul(line,'\n')=0;
        for(p=line+1;*p;) {
          for(q=OPTSTRING;*q;q++) if(*q==*p) {
            if(q[1]==':') {
              if(*++p==' ') ++p;
              set_option(*q,p);
              goto next;
            } else {
              set_option(*p++,"");
              break;
            }
          }
          if(!*q) errx(ERR_OPTION,"Improper switch");
        }
        next:;
      }
      fclose(f);
      free(line);
      break;
    case 'H': reqheaders=curl_slist_append(reqheaders,a); break;
    case 'I':
      v=strtol(a,&p,0)%10000;
      if(*p!='=') errx(ERR_OPTION,"Improper switch");
      if(u=curl_easy_setopt(m3ucurl,v+CURLOPTTYPE_LONG,(long)strtol(p+1,&p,0))) errx(ERR_CURL,"Improper curl option: %s",curl_easy_strerror(u));
      break;
    case 'N':
      v=strtol(a,&p,0)%10000;
      if(*p) errx(ERR_OPTION,"Improper switch");
      if(u=curl_easy_setopt(m3ucurl,v+CURLOPTTYPE_OBJECTPOINT,(char*)0)) errx(ERR_CURL,"Improper curl option: %s",curl_easy_strerror(u));
      break;
    case 'P': urlprefix=strdup(a); if(!urlprefix) err(ERR_MEMORY,"Allocation failed"); break;
    case 'S':
      v=strtol(a,&p,0)%10000;
      if(*p!='=') errx(ERR_OPTION,"Improper switch");
      if(u=curl_easy_setopt(m3ucurl,v+CURLOPTTYPE_OBJECTPOINT,p+1)) errx(ERR_CURL,"Improper curl option: %s",curl_easy_strerror(u));
      break;
    case 'c': commercial_skip=1; break;
    case 'e': endtime=iso8601_to_unix(a); break;
    case 'g': want_range=1; break;
    case 'l': log_out=fopen(a,"a"); if(!log_out) err(ERR_FILE,"Cannot open log file for appending"); setlinebuf(log_out); break;
    case 'm': maxtotal=parse_file_size(a); break;
    case 'n': maxsegments=strtol(a,0,0); break;
    case 'o': video_out=fopen(a,"a"); if(!video_out) err(ERR_FILE,"Cannot open video file for appending"); break;
    case 'p': want_progress=1; setbuf(stdout,0); puts("\e]0;hlsrecord\a"); break;
    case 'q': nodownload=1; break;
    case 'r': sscanf(a,"%d,%d,%d",&base_retry_time,&max_retry_time,&max_retry_count); break;
    case 's': starttime=iso8601_to_unix(a); break;
    case 't': if(*a<'a' || *a>'z') errx(ERR_OPTION,"Improper switch"); parse_time_interval(a+1,timing+*a-'a'); break;
    case 'u': if(baseurl) err(ERR_OPTION,"Multiple specifications of base URL"); baseurl=strdup(a); if(!baseurl) err(ERR_MEMORY,"Allocation failed"); break;
    case 'v': log_out=stderr; break;
    default: errx(ERR_OPTION,"Improper switch");
  }
}

int main(int argc,char**argv) {
  int c;
  char*u;
  timer1=timerfd_create(CLOCK_MONOTONIC,TFD_CLOEXEC);
  if(timer1==-1) err(ERR_OTHERS,"Cannot create timer");
  if(curl_global_init(CURL_GLOBAL_DEFAULT)) errx(ERR_CURL,"Error initializing curl");
  m3ucurl=curl_easy_init();
  if(!m3ucurl) errx(ERR_CURL,"Error initializing curl");
  curl_easy_setopt(m3ucurl,CURLOPT_USERAGENT,"hlsrecord");
  curl_easy_setopt(m3ucurl,CURLOPT_NOPROGRESS,(long)1);
  curl_easy_setopt(m3ucurl,CURLOPT_PROTOCOLS,(long)(CURLPROTO_HTTP|CURLPROTO_HTTPS|CURLPROTO_GOPHER)); // this may be removed in future; override this by -I181=-1 to avoid this restriction
  curl_easy_setopt(m3ucurl,CURLOPT_FAILONERROR,(long)1);
  tzset();
  while((c=getopt(argc,argv,"-" OPTSTRING))>0) set_option(c,optarg);
  if(!baseurl) errx(ERR_OPTION,"Base URL is not specified");
  if(reqheaders) curl_easy_setopt(m3ucurl,CURLOPT_HTTPHEADER,reqheaders);
  tscurl=curl_easy_duphandle(m3ucurl);
  if(!tscurl) errx(ERR_CURL,"Error initializing curl");
  curl_easy_setopt(m3ucurl,CURLOPT_WRITEFUNCTION,m3u_writer_callback);
  curl_easy_setopt(tscurl,CURLOPT_WRITEFUNCTION,video_writer_callback);
  if(want_range) curl_easy_setopt(tscurl,CURLOPT_HEADERFUNCTION,video_header_callback);
  curl_easy_setopt(m3ucurl,CURLOPT_SOCKOPTFUNCTION,m3u_sockopt_callback);
  curl_easy_setopt(m3ucurl,CURLOPT_URL,baseurl);
  srandom(begintime=time(0));
  if(log_out && video_out) affect_total(fprintf(log_out,"BEG:%llu,%lld\n",(long long)ftello(video_out),(long long)begintime));
  for(;;) {
    timer_flag=0;
    retry_count=0;
    m3u_reset();
    if(want_progress) show_progress("m-");
    if(log_out) affect_total(fprintf(log_out,"GET:%lld,%s\n",(long long)time(0),baseurl));
    while(c=curl_easy_perform(m3ucurl)) {
      // This program should check if the error is known to be permanent, but it currently doesn't.
      int j=base_retry_time<<retry_count;
      long q;
      struct timespec x={.tv_sec=j?random()%(j<max_retry_time?j+1:max_retry_time+1):0,.tv_nsec=j?random()%999999999:1};
      if(log_out) {
        affect_total(c==CURLE_HTTP_RETURNED_ERROR?fprintf(log_out,"ERR:HTTP:%ld\n",(curl_easy_getinfo(m3ucurl,CURLINFO_RESPONSE_CODE,&q),q)):fprintf(log_out,"ERR:CURL:%d\n",c));
      }
      if(retry_count++==max_retry_count) errx(ERR_CURL,"Curl error %d: %s",c,curl_easy_strerror(c));
      if(nanosleep(&x,0) && errno!=EINTR) err(ERR_OTHERS,"Error with nanosleep");
    }
    fclose(segments_file);
    if(nsegments && !segments_str) err(ERR_MEMORY,"Segment error");
    u=segments_str;
    for(c=0;c<nsegments;c++) {
      do_segment(u);
      u+=strlen(u)+1;
    }
    if(!video_out) break; // Measurement mode only
    if(ended || ended_program) break;
    playlist_wait();
  }
  if(log_out && video_out) fprintf(log_out,"END:%llu,%lld,%d,%d\n",(long long)ftello(video_out),(long long)time(0),ended,ended_program);
  if(!video_out) {
    printf("TIME_ELAPSED=%lld\n",(long long)(time(0)-begintime));
    printf("FIRST_TIME_OFFSET=%lld\n",(long long)(first_time-begintime));
    printf("LAST_TIME_OFFSET=%lld\n",(long long)(last_time-begintime));
    printf("END_TIME_OFFSET=%lld\n",(long long)(last_time-time(0)));
    printf("TARGET_DURATION=%lld.%09ld\n",(long long)targetduration.tv_sec,(long)targetduration.tv_nsec);
    printf("VIDEO_TIME=%lld.%09ld\n",(long long)totalsegtime.tv_sec,(long)totalsegtime.tv_nsec);
    printf("VIDEO_SIZE=%llu\n",(long long)video_total);
    printf("NUM_SEGMENTS=%u\n",nsegments);
    printf("BIT_RATE=%g\n",(8.0*video_total)/(double)(totalsegtime.tv_sec+totalsegtime.tv_nsec*1.0e-9));
  }
  if(want_progress) show_progress("..");
  return 0;
}

#if 0
gcc -g -O1 -o ~/bin/hlsrecord -fwrapv hlsrecord.c aes.o -lm -lrt `curl-config --cflags --libs`
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
#include "aes.h"

#define ERR_OPTION 3
#define ERR_M3U 4
#define ERR_CURL 5
#define ERR_MEMORY 6
#define ERR_URL 7
#define ERR_FILE 8
#define ERR_OTHERS 9
#define ERR_LIMIT 10
#define ERR_CRITERIA 11

#define M3ULINEMAX 6000

#define ATTR_NONE 0
#define ATTR_INTEGER 1
#define ATTR_FLOAT 2
#define ATTR_HEX 3
#define ATTR_STRING 4
#define ATTR_ENUM 5
#define ATTR_RESOLUTION 6
#define ATTR_EMPTY 7
#define ATTR_ERROR 8

typedef struct {
  const char*name;
  uint8_t*ptype;
  uint64_t*pint;
  struct timespec*pfloat;
  uint8_t*phex;
  uint8_t*pstring;
  size_t*plen;
  size_t maxlen;
  uint8_t*penum;
  const char*senum;
  uint32_t*presx;
  uint32_t*presy;
} Attribute;

static time_t starttime,endtime;
static uint64_t maxtotal=0xFFFFFFFFFFFFFFFFULL;
static uint16_t maxsegments=0xFFFF;
static char*baseurl;
static char*urlprefix;
static struct curl_slist*reqheaders;
static FILE*log_out;
static FILE*video_out;
static int base_retry_time,max_retry_time,max_retry_count,retry_count;
static struct timespec timing[26];
static char commercial_skip,want_range,want_progress,use_client_clock;
static char nodownload,force_insecure,is_master;

static CURL*m3ucurl;
static CURL*tscurl;
static CURL*keycurl;
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
// Each entry is one of:
//   Null-terminated URL of media segment (counts toward nsegments)
//   Null-terminated URL of key, preceded by 0x01
//   Initialization vector (sixteen bytes), preceded by 0x02

static int timer1,timer_flag;
static struct timespec request_time;

static const struct timespec zerotime={};

static uint8_t key_method;
static uint8_t key_url[M3ULINEMAX];
static uint8_t key_saved_url[M3ULINEMAX];
static uint8_t key_iv[16];
static uint8_t key_iv_type=ATTR_NONE;
static const Attribute x_key_attrib[]={
  {
    .name="METHOD",
    .penum=&key_method,
    .senum="NONE,AES-128,SAMPLE-AES",
  },
  {
    .name="URI",
    .pstring=key_url,
    .maxlen=M3ULINEMAX-2,
  },
  {
    .name="IV",
    .ptype=&key_iv_type,
    .phex=key_iv,
    .maxlen=16,
  },
};

static struct AES_ctx aes_ctx;
static uint8_t aes_key[16];
static uint8_t aes_offs;
static uint8_t encrypted;
static uint8_t ciphertext[16];
static uint8_t ciphertext_offs;

typedef union {
  uint64_t i;
  struct timespec f;
  char*s;
} CriteriaValue;

#define CRITERIA_INTEGER 0x01
#define CRITERIA_FLOAT 0x02
#define CRITERIA_STRING 0x04
#define CRITERIA_LESS 0x10 // actually means less or equal
#define CRITERIA_GREATER 0x20 // actually means greater or equal
#define CRITERIA_PREFER_LOWEST 0x40
#define CRITERIA_PREFER_HIGHEST 0x80

typedef struct {
  CriteriaValue mini,maxi;
  uint8_t type;
} Criteria;

typedef struct {
  uint64_t bandwidth;
  uint64_t average_bandwidth;
  uint8_t codecs[1024];
  uint32_t resx,resy;
  struct timespec framerate;
  uint8_t hdcp;
} MasterInfo;

static MasterInfo master,bestmaster;
static uint8_t playlist_url[M3ULINEMAX];

static Criteria criteria_bandwidth={.mini.i=0,.maxi.i=0xFFFFFFFFFFFFFFFFULL,.type=CRITERIA_INTEGER};
static Criteria criteria_average_bandwidth={.mini.i=0,.maxi.i=0xFFFFFFFFFFFFFFFFULL,.type=CRITERIA_INTEGER};
static Criteria criteria_codecs={.type=CRITERIA_STRING};
static Criteria criteria_resx={.mini.i=0,.maxi.i=0xFFFFFFFFFFFFFFFFULL,.type=CRITERIA_INTEGER};
static Criteria criteria_resy={.mini.i=0,.maxi.i=0xFFFFFFFFFFFFFFFFULL,.type=CRITERIA_INTEGER};
static Criteria criteria_framerate={.mini.f={0,0},.maxi.f={999999999,0},.type=CRITERIA_FLOAT};
static Criteria criteria_hdcp={.mini.i=0,.maxi.i=0,.type=CRITERIA_INTEGER};
static uint8_t criteria_order[12];
static uint8_t criteria_norder=0;

static const Attribute x_stream_inf_attrib[]={
  {
    .name="BANDWIDTH",
    .pint=&master.bandwidth,
  },
  {
    .name="AVERAGE-BANDWIDTH",
    .pint=&master.average_bandwidth,
  },
  {
    .name="CODECS",
    .pstring=master.codecs,
    .maxlen=1022,
  },
  {
    .name="RESOLUTION",
    .presx=&master.resx,
    .presy=&master.resy,
  },
  {
    .name="FRAME-RATE",
    .pfloat=&master.framerate,
  },
  {
    .name="HDCP-LEVEL",
    .penum=&master.hdcp,
    .senum="NONE,TYPE-0",
  },
};

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
    if(force_insecure && n==5 && (rel[0]=='H' || rel[0]=='h') && (rel[1]=='T' || rel[1]=='t') && (rel[2]=='T' || rel[2]=='t') && (rel[3]=='P' || rel[3]=='p') && (rel[4]=='S' || rel[4]=='s')) {
      fputs("http",out);
    } else {
      for(n=0;rel[n]!=':';n++) {
        if(rel[n]>='A' && rel[n]<='Z') fputc(rel[n]+'a'-'A',out); else fputc(rel[n],out);
      }
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
  char neg=(*in=='-');
  *out=(struct timespec){};
  if(neg) in++;
  while(*in>='0' && *in<='9') out->tv_sec=10*out->tv_sec+*in++-'0';
  if(neg) out->tv_sec*=-1;
  if(*in++=='.') {
    long u=1000000000L;
    while(*in>='0' && *in<='9' && u) out->tv_nsec+=(*in++-'0')*(u/=10);
  }
}

static int parse_attribute_list(const char*text,const Attribute*attr,int count) {
  const char*p;
  static const Attribute noattr={};
  const Attribute*a=0;
  char m[40];
  int i;
  uint64_t u,v;
  for(i=0;i<count;i++) if(attr[i].ptype) attr[i].ptype[0]=ATTR_NONE;
  while(*text==' ' || *text=='\t') ++text;
  next:
  while(*text==',') ++text;
  if(!*text) return 0;
  for(i=0;i<39 && ((text[i]>='A' && text[i]<='Z') || (text[i]>='0' && text[i]<='9') || text[i]=='-');i++);
  if(!i || (text[i]!='=' && text[i] && text[i]!=',') || i==39) return -1;
  memcpy(m,text,i);
  m[i]=0;
  text+=i;
  a=&noattr;
  for(i=0;i<count;i++) if(!strcmp(attr[i].name,m)) {
    a=attr+i;
    break;
  }
  if(*text=='=') text++;
  switch(*text) {
    case 0: case ',': // nothing
      if(a->ptype) a->ptype[0]=ATTR_EMPTY;
      goto next;
    case '0' ... '9': case '.': case '-': // integer, float, hex, resolution
      if(*text=='0' && (text[1]=='X' || text[1]=='x')) {
        if(a->ptype) a->ptype[0]=ATTR_HEX;
        text+=2;
        if(a->presx) a->presx[0]=0;
        if(a->presy) a->presy[0]=strtoul(text,0,10);
        for(u=0;;u++) {
          if(text[0]>='0' && text[0]<='9') v=text[0]-'0'; else if(text[0]>='A' && text[0]<='F') v=text[0]+10-'A'; else break;
          v<<=4;
          if(text[1]>='0' && text[1]<='9') v+=text[1]-'0'; else if(text[1]>='A' && text[1]<='F') v+=text[1]+10-'A'; else break;
          text+=2;
          if(u<a->maxlen && a->phex) a->phex[u]=v;
        }
        if(a->plen) a->plen[0]=u;
      } else {
        u=ATTR_INTEGER;
        for(p=text;*p && *p!=',' && *p!='"';p++) {
          if(*p=='.' || *p=='-') u=ATTR_FLOAT;
          if(*p=='x') u=ATTR_RESOLUTION;
        }
        if(a->ptype) a->ptype[0]=u;
        if(u==ATTR_INTEGER) {
          if(a->pfloat) parse_time_interval(text,a->pfloat);
          if(a->pint) a->pint[0]=strtoull(text,0,10);
        } else if(u==ATTR_FLOAT) {
          if(a->pfloat) parse_time_interval(text,a->pfloat);
        } else if(u==ATTR_RESOLUTION) {
          u=strtoul(text,(char**)&p,10);
          if(*p=='x') v=strtoul(p+1,0,10); else v=0;
          if(a->presx) a->presx[0]=u;
          if(a->presy) a->presy[0]=v;
        }
      }
      break;
    case '"': // string
      text++;
      u=0;
      while(*text && *text!='"' && *text!='\r' && *text!='\n') {
        if(u<a->maxlen && a->pstring) a->pstring[u]=*text;
        u++; text++;
      }
      if(a->ptype) a->ptype[0]=ATTR_STRING;
      if(u<a->maxlen && a->pstring) a->pstring[u]=0;
      if(a->plen) a->plen[0]=u;
      break;
    default: // enumerated
      if(a->ptype) a->ptype[0]=ATTR_ERROR;
      if(p=a->senum) {
        for(v=0;;v++) {
          for(u=0;text[u] && text[u]!=',' && text[u]==*p;u++,p++);
          if((*p==',' || !*p) && (text[u]==',' || !text[u])) {
            if(a->penum) a->penum[0]=v;
            if(a->ptype) a->ptype[0]=ATTR_ENUM;
            break;
          }
          if(p=strchr(p,',')) p++; else break;
        }
      }
  }
  while(*text && *text!=',') ++text;
  goto next;
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

static inline int compare_timespec(const struct timespec*a,const struct timespec*b) {
  return a->tv_sec<b->tv_sec?-1:a->tv_sec>b->tv_sec?1:a->tv_nsec<b->tv_nsec?-1:a->tv_nsec>b->tv_nsec?1:0;
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
  uint64_t s=size*nmemb;
  video_total+=s;
  received_length+=s;
  affect_total(s);
  if(video_out) {
    if(!encrypted) {
      fwrite(ptr,size,nmemb,video_out);
    } else {
      uint8_t u=ciphertext_offs;
      if(u) {
        int c=16-u;
        if(c>s) c=s;
        memcpy(ciphertext+u,ptr,c);
        ciphertext_offs=u=(u+c)&15;
        if(u) goto skip;
        AES_CBC_decrypt_buffer(&aes_ctx,ciphertext,16);
        fwrite(ciphertext,1,16,video_out);
        ptr+=c; s-=c;
      }
      if(s&~15) {
        AES_CBC_decrypt_buffer(&aes_ctx,ptr,s&~15);
        fwrite(ptr,1,s&~15,video_out);
        ptr+=s&~15; s&=15;
      }
      if(s) memcpy(ciphertext,ptr,ciphertext_offs=s);
    }
  }
  skip:
  if(want_progress) show_progress("v+");
  return size*nmemb;
}

static size_t key_writer_callback(char *ptr, size_t size, size_t nmemb, void *userdata) {
  size_t n;
  size*=nmemb;
  if(aes_offs<16) {
    n=16-aes_offs;
    if(n>size) n=size;
    memcpy(aes_key+aes_offs,ptr,16-aes_offs);
    aes_offs+=n;
  }
  if(want_progress) show_progress("k+");
  return size;
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

#define CRITERIA_DO_INTEGER(b) \
 if(((criteria_##b.type&CRITERIA_LESS) && master.b>criteria_##b.maxi.i) || ((criteria_##b.type&CRITERIA_GREATER) && master.b<criteria_##b.mini.i)) return;
#define CRITERIA_DO_FLOAT(b) \
 if(((criteria_##b.type&CRITERIA_LESS) && compare_timespec(&master.b,&criteria_##b.mini.f)>0) || ((criteria_##b.type&CRITERIA_GREATER) && compare_timespec(&master.b,&criteria_##b.mini.f)<0)) return;
#define CRITERIA_BEST_INTEGER(a,b) case a: \
 if(criteria_##b.type&CRITERIA_PREFER_LOWEST) { if(master.b<bestmaster.b) goto best; else if(master.b>bestmaster.b) return; } \
 if(criteria_##b.type&CRITERIA_PREFER_HIGHEST) { if(master.b>bestmaster.b) goto best; else if(master.b<bestmaster.b) return; } \
 break;
#define CRITERIA_BEST_FLOAT(a,b) case a: {int i=compare_timespec(&master.b,&bestmaster.b); \
  if(criteria_##b.type&CRITERIA_PREFER_LOWEST) { if(i<0) goto best; else if(i>0) return; } \
  if(criteria_##b.type&CRITERIA_PREFER_HIGHEST) { if(i>0) goto best; else if(i<0) return; } \
 }break;

static void m3u_process_line(void) {
  if(log_out) affect_total(fprintf(log_out,"M3U:%s\n",m3uline));
  if(!memcmp(m3uline,"#EXT",4)) {
    // Command
    char*p=strchr(m3uline+4,':');
    if(p) *p++=0;
    if(!strcmp(m3uline+4,"INF") && p) {
      if(*p=='-') return; // Ignore this line if the duration is negative, since some files that do not follow the specification use this for extra TV attributes.
      parse_time_interval(p,&segtime);
      if(segtime.tv_sec>=0) add_timespec(&segtime,&totalsegtime);
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
    } else if(p && !is_master && !strcmp(m3uline+4,"-X-KEY")) {
      key_method=255;
      key_iv_type=0;
      *key_url=0;
      parse_attribute_list(p,x_key_attrib,sizeof(x_key_attrib)/sizeof(Attribute));
      if(key_method>1) errx(ERR_M3U,"Unimplemented encryption type");
      if(key_method && *key_url) {
        if(strcmp(key_url,key_saved_url)) {
          fputc(1,segments_file);
          convert_url(baseurl,key_url,segments_file);
          fputc(0,segments_file);
          memcpy(key_saved_url,key_url,M3ULINEMAX);
        }
      }
    } else if(p && is_master && !strcmp(m3uline+4,"-X-STREAM-INF")) {
      master.bandwidth=criteria_bandwidth.mini.i;
      master.average_bandwidth=0;
      *master.codecs=0;
      master.resx=master.resy=0;
      master.framerate=(struct timespec){30,0};
      master.hdcp=0;
      parse_attribute_list(p,x_stream_inf_attrib,sizeof(x_stream_inf_attrib)/sizeof(Attribute));
      if(!master.average_bandwidth) master.average_bandwidth=master.bandwidth;
    } else if(!strcmp(m3uline+4,"-X-ENDLIST")) {
      ended=1;
    }
  } else if(is_master && *m3uline && *m3uline!='#') {
    CRITERIA_DO_INTEGER(bandwidth);
    CRITERIA_DO_INTEGER(average_bandwidth);
    CRITERIA_DO_INTEGER(resx);
    CRITERIA_DO_INTEGER(resy);
    CRITERIA_DO_INTEGER(hdcp);
    CRITERIA_DO_FLOAT(framerate);
    if((criteria_codecs.type&CRITERIA_LESS) && strcmp(criteria_codecs.mini.s,master.codecs)) return; //TODO: more elaborate handling of codecs
    if(nsegments && criteria_norder) {
      int i;
      for(i=0;i<criteria_norder;i++) {
        switch(criteria_order[i]) {
          CRITERIA_BEST_INTEGER('A',average_bandwidth);
          CRITERIA_BEST_INTEGER('B',bandwidth);
          CRITERIA_BEST_FLOAT('F',framerate);
          CRITERIA_BEST_INTEGER('H',hdcp);
          CRITERIA_BEST_INTEGER('x',resx);
          CRITERIA_BEST_INTEGER('y',resy);
        }
      }
    }
    best:
    bestmaster=master;
    rewind(segments_file);
    convert_url(baseurl,m3uline,segments_file);
    fputc(0,segments_file);
    nsegments=1;
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
      if(key_method) {
        fputc(2,segments_file);
        if(key_iv_type==ATTR_HEX) {
          fwrite(key_iv,1,16,segments_file);
        } else {
          fputc(seqnumber>>070,segments_file);
          fputc(seqnumber>>060,segments_file);
          fputc(seqnumber>>050,segments_file);
          fputc(seqnumber>>040,segments_file);
          fputc(seqnumber>>030,segments_file);
          fputc(seqnumber>>020,segments_file);
          fputc(seqnumber>>010,segments_file);
          fputc(seqnumber>>000,segments_file);
        }
      }
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
  key_method=0;
}

static void do_segment(const char*url) {
  int c;
  CURL*z=tscurl;
  if(*url==1) z=keycurl,url++,aes_offs=0;
  if(log_out) affect_total(fprintf(log_out,"%s:%llu,%s\n",z==tscurl?"SEG":"KEY",(long long)(video_out?ftello(video_out):0),url));
  if(nodownload) return;
  if(urlprefix) {
    for(c=0;urlprefix[c];c++) if(url[c]!=urlprefix[c]) {
      if(log_out) fprintf(log_out,"ERR:URL_PREFIX\n");
      errx(ERR_URL,"The required URL prefix does not match");
    }
  }
  content_length=0; received_length=0; ciphertext_offs=0;
  curl_easy_setopt(z,CURLOPT_URL,url);
  if(want_range && z==tscurl) curl_easy_setopt(tscurl,CURLOPT_RANGE,(char*)0);
  repeat:
  if(want_progress) show_progress(z==tscurl?"v-":"k-");
  while(c=curl_easy_perform(z)) {
    // This program should check if the error is known to be permanent, but it currently doesn't.
    int j=base_retry_time<<retry_count;
    long q;
    struct timespec x={.tv_sec=j?random()%(j<max_retry_time?j+1:max_retry_time+1):0,.tv_nsec=j?random()%999999999:1};
    if(log_out) {
      if(video_out) fprintf(log_out,"ATO:%llu\n",(long long)ftello(video_out));
      affect_total(c==CURLE_HTTP_RETURNED_ERROR?fprintf(log_out,"ERR:HTTP:%ld\n",(curl_easy_getinfo(z,CURLINFO_RESPONSE_CODE,&q),q)):fprintf(log_out,"ERR:CURL:%d\n",c));
    }
    if(retry_count++==max_retry_count) errx(ERR_CURL,"Curl error %d: %s",c,curl_easy_strerror(c));
    if(nanosleep(&x,0) && errno!=EINTR) err(ERR_OTHERS,"Error with nanosleep");
  }
  if(want_range && z==tscurl && received_length<content_length) {
    //TODO: Scorpion range requests, which work differently from HTTP. (This also does not work with RTSP.)
    char buf[64];
    snprintf(buf,64,"%llu-%llu",(unsigned long long)received_length,(unsigned long long)(content_length-1));
    curl_easy_setopt(tscurl,CURLOPT_RANGE,buf);
    if(log_out) affect_total(fprintf(log_out,"TRY:%s\n",buf));
    if(retry_count++==max_retry_count) errx(ERR_OTHERS,"Reached maximum retry count with range request");
    goto repeat;
  }
  if(encrypted && video_out && (c=ciphertext_offs)) {
    memset(ciphertext+c,16-c,16-c);
    AES_CBC_decrypt_buffer(&aes_ctx,ciphertext,16);
    fwrite(ciphertext,1,c,video_out);
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

static void read_master_criteria_value(Criteria*c,uint8_t t,const char*a) {
  // t:  1 >=  2 <=  5 >  6 <
  CriteriaValue v;
  if(c->type&CRITERIA_INTEGER) {
    v.i=strtoll(a,0,10);
    if(t==5) v.i++; else if(t==6) v.i--;
  }
  if(c->type&CRITERIA_FLOAT) parse_time_interval(a,&v.f);
  if(t&1) c->mini=v; else if(t&2) c->maxi=v;
}

static void read_master_criteria(const char*a) {
  Criteria*c=0;
  if(criteria_norder==12) errx(ERR_OPTION,"Too many variant selection criteria");
  criteria_order[criteria_norder]=*a;
  switch(*a++) {
    case 'A': c=&criteria_average_bandwidth; break;
    case 'B': c=&criteria_bandwidth; break;
    case 'F': c=&criteria_framerate; break;
    case 'H': c=&criteria_hdcp; break;
    case 'c': c=&criteria_codecs; break;
    case 'x': c=&criteria_resx; break;
    case 'y': c=&criteria_resy; break;
    default: errx(ERR_OPTION,"Improper variant selection criteria");
  }
  if(c->type&CRITERIA_STRING) {
    if(*a++!='=') errx(ERR_OPTION,"Improper variant selection criteria");
    c->type=CRITERIA_LESS|CRITERIA_GREATER|CRITERIA_STRING;
    c->mini.s=strdup(a);
    c->maxi.s=c->mini.s;
    return;
  }
  if(*a=='L' || *a=='H') {
    if(!(c->type&(CRITERIA_PREFER_LOWEST|CRITERIA_PREFER_HIGHEST))) criteria_norder++;
    c->type|=(*a=='L'?CRITERIA_PREFER_LOWEST:CRITERIA_PREFER_HIGHEST);
    if(!*++a) return;
  }
  switch(*a++) {
    case '=':
      c->type|=CRITERIA_LESS|CRITERIA_GREATER;
      read_master_criteria_value(c,1,a);
      c->maxi=c->mini;
      break;
    case '<':
      c->type|=CRITERIA_LESS;
      if(*a=='=') read_master_criteria_value(c,2,a+1); else read_master_criteria_value(c,6,a);
      break;
    case '>':
      c->type|=CRITERIA_GREATER;
      if(*a=='=') read_master_criteria_value(c,1,a+1); else read_master_criteria_value(c,5,a);
      break;
    case ':':
      c->type|=CRITERIA_LESS|CRITERIA_GREATER;
      read_master_criteria_value(c,1,a);
      a=strchr(a,':');
      if(!a) errx(ERR_OPTION,"Improper variant selection criteria");
      read_master_criteria_value(c,2,a+1);
      break;
    default: errx(ERR_OPTION,"Improper variant selection criteria");
  }
}

#define OPTSTRING "H:I:KM:N:P:S:cde:gl:m:n:o:pqr:s:t:u:v"

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
    case 'K': force_insecure=1; break;
    case 'M':
      if(!is_master) is_master=1;
      if(*a=='0') is_master=2; else read_master_criteria(a);
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
    case 'd': use_client_clock=1; break;
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
  keycurl=curl_easy_duphandle(m3ucurl);
  if(!tscurl || !keycurl) errx(ERR_CURL,"Error initializing curl");
  curl_easy_setopt(m3ucurl,CURLOPT_WRITEFUNCTION,m3u_writer_callback);
  curl_easy_setopt(tscurl,CURLOPT_WRITEFUNCTION,video_writer_callback);
  curl_easy_setopt(keycurl,CURLOPT_WRITEFUNCTION,key_writer_callback);
  if(want_range) curl_easy_setopt(tscurl,CURLOPT_HEADERFUNCTION,video_header_callback);
  curl_easy_setopt(m3ucurl,CURLOPT_SOCKOPTFUNCTION,m3u_sockopt_callback);
  curl_easy_setopt(m3ucurl,CURLOPT_URL,baseurl);
  srandom(begintime=time(0));
  if(log_out && video_out) affect_total(fprintf(log_out,"BEG:%llu,%lld\n",(long long)ftello(video_out),(long long)begintime));
  if(is_master) {
    if(log_out) affect_total(fprintf(log_out,"MAS:%d\n",is_master));
    segments_file=fmemopen(playlist_url,M3ULINEMAX-1,"w+");
    if(want_progress) show_progress("M-");
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
    if(!nsegments) errx(ERR_CRITERIA,"No valid media playlists that match your specified criteria have been found");
    fclose(segments_file);
    if(want_progress) show_progress("M.");
    if(baseurl!=(void*)playlist_url) free(baseurl);
    baseurl=playlist_url;
    if(is_master==2) {
      puts(baseurl);
      return 0;
    }
    is_master=0;
    if(log_out) affect_total(fprintf(log_out,"MAS:%d\n",is_master));
    curl_easy_setopt(m3ucurl,CURLOPT_URL,baseurl);
  }
  for(;;) {
    timer_flag=0;
    retry_count=0;
    m3u_reset();
    if(want_progress) show_progress("m-");
    if(log_out) affect_total(fprintf(log_out,"GET:%lld,%s\n",(long long)time(0),baseurl));
    if(use_client_clock) {
      time_t t=time(0);
      if(starttime && t<starttime) criteria=2;
      if(endtime && t>=endtime) criteria=0,ended_program=1;
      if(!first_time) first_time=t;
      last_time=t;
    }
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
    encrypted=0;
    u=segments_str;
    for(c=0;c<nsegments;c++) {
      if(*u!=2) {
        do_segment(u);
        if(*u==1) c--; else encrypted=0;
        u+=strlen(u)+1;
      } else {
        AES_init_ctx_iv(&aes_ctx,aes_key,u+1);
        u+=17;
        c--;
        encrypted=1;
      }
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

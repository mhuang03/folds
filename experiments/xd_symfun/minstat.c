/* Tropical (min / max) subset DP for set-computable statistics: one byte per set, so
   N <= 31 fits in 2.2 GB.   usage: minstat N mode    mode = t_des | t_pk | a_exc
   prints "N mode min max".  (t_des = number of inverse descents of the fold sequence:
   #{m : panel m+1 is placed before panel m}.) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
int main(int argc,char**argv){
  int N=atoi(argv[1]); const char*mode=argv[2]; u64 full=(1ULL<<N)-1, L[64],R[64];
  int md = !strcmp(mode,"t_des")?0 : !strcmp(mode,"t_pk")?1 : 2;
  for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m;L[m]=R[m]=0;
    for(int d=1;d<=r;d++){L[m]|=1ULL<<(m-d-1);R[m]|=1ULL<<(m+d-1);}}
  int res[2];
  for(int pass=0;pass<2;pass++){           /* pass 0: min, pass 1: max */
    unsigned char *g=malloc(full+1); if(!g){fprintf(stderr,"oom\n");return 1;}
    memset(g,255,full+1); g[0]=0;          /* 255 = unreachable */
    for(u64 S=0;S<full;S++){ unsigned v=g[S]; if(v==255)continue; int k=__builtin_popcountll(S);
      for(int m=1;m<=N;m++){u64 b=1ULL<<(m-1); if(S&b)continue;
        if(__builtin_popcountll(S&L[m])!=__builtin_popcountll(S&R[m]))continue;
        int inc = md==0 ? (m<N && (S>>m&1)) : md==1 ? (m>1&&m<N&&(S>>m&1)&&(S>>(m-2)&1)) : (m>k+1);
        unsigned w=v+inc; unsigned char *d=g+(S|b);
        if(*d==255 || (pass==0 ? w<*d : w>*d)) *d=w; } }
    res[pass]=g[full]; free(g);
  }
  printf("%d %s %d %d\n",N,mode,res[0],res[1]); return 0; }

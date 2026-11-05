/* Generic subset DP for fold-sequence variants.
   usage: dp N mode [param] [outfile]
   modes: semi   full semi-symmetric condition
          sym    symmetric (3-AP-free)
          left   only panels m <= (N+1)/2 constrained
          mod2   counts equal mod 2
          cyc    Z_N, radius floor((N-1)/2) for every panel (rotation invariant)
          one    only panel `param` constrained
          cap    radius min(m-1,N-m,param)
          ge     left count >= right count (one-sided inequality)
          csym   cyclic symmetric on Z_N (3-AP-free mod N analogue)
          cmod2  cyclic, radius floor((N-1)/2), counts equal mod 2
          ccap   cyclic, radius min(floor((N-1)/2), param)
   writes g[S] (uint64, 2^N entries) to outfile if given; prints g[full]. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc,char**argv){
  int N=atoi(argv[1]); const char*mode=argv[2]; int par=argc>3?atoi(argv[3]):0;
  const char*out=argc>4?argv[4]:0;
  uint64_t full=(1ULL<<N)-1;
  uint64_t *g=calloc(1ULL<<N,8);
  uint64_t L[64],R[64]; int con[64];
  for(int m=1;m<=N;m++){
    int D=m-1<N-m?m-1:N-m; L[m]=R[m]=0; con[m]=1;
    if(!strcmp(mode,"cap")&&D>par)D=par;
    if(!strcmp(mode,"cyc")||!strcmp(mode,"csym")||!strcmp(mode,"cmod2")||!strcmp(mode,"ccap")){ D=(N-1)/2; if(!strcmp(mode,"ccap")&&D>par)D=par;
      for(int d=1;d<=D;d++){ L[m]|=1ULL<<(((m-1-d)%N+N)%N); R[m]|=1ULL<<((m-1+d)%N);} }
    else for(int d=1;d<=D;d++){L[m]|=1ULL<<(m-d-1);R[m]|=1ULL<<(m+d-1);}
    if(!strcmp(mode,"left")) con[m]= (2*m<=N+1);
    if(!strcmp(mode,"one")) con[m]= (m==par);
  }
  int md=!strcmp(mode,"mod2")||!strcmp(mode,"cmod2"), sy=!strcmp(mode,"sym"), ge=!strcmp(mode,"ge"), csy=!strcmp(mode,"csym");
  g[0]=1;
  for(uint64_t S=0;S<full;S++){ uint64_t c=g[S]; if(!c)continue;
    for(int m=1;m<=N;m++){ uint64_t b=1ULL<<(m-1); if(S&b)continue;
      int ok=1;
      if(con[m]){
        int a=__builtin_popcountll(S&L[m]), r=__builtin_popcountll(S&R[m]);
        if(md) ok=((a^r)&1)==0;
        else if(ge) ok=a>=r;
        else if(csy){ int D=(N-1)/2; for(int d=1;d<=D&&ok;d++) ok=(((S>>(((m-1-d)%N+N)%N))&1)==((S>>((m-1+d)%N))&1)); }
        else if(sy){ int D=m-1<N-m?m-1:N-m; for(int d=1;d<=D&&ok;d++) ok=(((S>>(m-d-1))&1)==((S>>(m+d-1))&1)); }
        else ok=(a==r);
      }
      if(ok) g[S|b]+=c; } }
  printf("%llu\n",(unsigned long long)g[full]);
  if(out){FILE*f=fopen(out,"wb");fwrite(g,8,1ULL<<N,f);fclose(f);}
  return 0;
}

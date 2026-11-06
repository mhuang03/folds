/* maxpath.c -- max over valid sequences of sum_k log V(S_k) (tree bound), with an optimal path.
   usage: ./maxpath N.  Memory: 2^N * 4 bytes (float). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
int N; uint64_t Lm[64], Rm[64];
static inline uint32_t valid(uint64_t S){ uint32_t v=0;
  for(int m=1;m<=N;m++){uint64_t b=1ULL<<(m-1); if(S&b)continue;
    if(__builtin_popcountll(S&Lm[m])==__builtin_popcountll(S&Rm[m])) v|=(uint32_t)b;} return v;}
int main(int argc,char**argv){N=atoi(argv[1]); uint64_t NS=1ULL<<N, full=NS-1;
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m; Lm[m]=Rm[m]=0;
    for(int d=1;d<=D;d++){Lm[m]|=1ULL<<(m-d-1);Rm[m]|=1ULL<<(m+d-1);}}
  float *M=malloc(NS*sizeof(float)); M[full]=0;
  for(uint64_t S=full;S-->0;){uint32_t v=valid(S); int deg=__builtin_popcount(v); float best=-1;
    while(v){int i=__builtin_ctz(v); v&=v-1; float t=M[S|(1ULL<<i)]; if(t>best)best=t;}
    M[S]= best<0? -1 : best+logf((float)deg);}
  double lf=lgamma(N+1.0);
  printf("N=%d logMV=%.4f logN!=%.4f deficit=%.4f deficit/N=%.4f\n",N,M[0],lf,lf-M[0],(lf-M[0])/N);
  uint64_t S=0; printf("path:"); for(int k=0;k<N;k++){uint32_t v=valid(S); int deg=__builtin_popcount(v); float best=-1;int bi=-1;
    while(v){int i=__builtin_ctz(v); v&=v-1; float t=M[S|(1ULL<<i)]; if(t>best){best=t;bi=i;}}
    printf(" %d(%d/%d)",bi+1,deg,N-k); S|=1ULL<<bi;} printf("\n"); return 0;}

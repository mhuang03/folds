/* minpath.c -- exact min over valid sequences of additive path costs (subset DP, N <= ~27).
   usage: ./minpath N mode
     mode 0: cost(S)   = bad(S)  = #{m free, not valid at S}            (sum_k (f_k - V_k))
     mode 1: cost(S)   = odd(S)  = #{m free, |S cap W_m| odd}
     mode 2: cost(S,m) = |S cap (W_m \ m)| = 2 A_m                      (kick count C)
     mode 3: cost(S)   = ln(f/V(S))   (path deficit)
   Prints min, min/N^2, and an optimal path. Memory 2^N * 4 bytes. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
int N, mode; uint64_t Lm[64], Rm[64];
static inline uint32_t valid(uint64_t S){ uint32_t v=0;
  for(int m=1;m<=N;m++){uint64_t b=1ULL<<(m-1); if(S&b)continue;
    if(__builtin_popcountll(S&Lm[m])==__builtin_popcountll(S&Rm[m])) v|=(uint32_t)b;} return v;}
static inline int oddc(uint64_t S){ int c=0;
  for(int m=1;m<=N;m++){uint64_t b=1ULL<<(m-1); if(S&b)continue;
    if(__builtin_popcountll(S&(Lm[m]|Rm[m]))&1) c++;} return c;}
int main(int argc,char**argv){N=atoi(argv[1]); mode=atoi(argv[2]);
  uint64_t NS=1ULL<<N, full=NS-1;
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m; Lm[m]=Rm[m]=0;
    for(int d=1;d<=D;d++){Lm[m]|=1ULL<<(m-d-1);Rm[m]|=1ULL<<(m+d-1);}}
  float *M=malloc(NS*sizeof(float)); M[full]=0;
  for(uint64_t S=full;S-->0;){uint32_t v=valid(S); int deg=__builtin_popcount(v); float best=1e30f;
    int f=N-__builtin_popcountll(S);
    while(v){int i=__builtin_ctz(v); v&=v-1; float t=M[S|(1ULL<<i)];
      if(mode==2) t+=__builtin_popcountll(S&(Lm[i+1]|Rm[i+1]));
      if(t<best)best=t;}
    float c=0; if(mode==0) c=f-deg; else if(mode==1) c=oddc(S); else if(mode==3) c=logf((float)f/deg);
    M[S]= best>1e29f? 1e30f : best+c;}
  printf("N=%d mode=%d min=%.4f min/N^2=%.5f min/N=%.4f\n",N,mode,M[0],M[0]/((double)N*N),M[0]/N);
  uint64_t S=0; printf("path:"); for(int k=0;k<N;k++){uint32_t v=valid(S); int deg=__builtin_popcount(v); float best=1e30f;int bi=-1;
    while(v){int i=__builtin_ctz(v); v&=v-1; float t=M[S|(1ULL<<i)];
      if(mode==2) t+=__builtin_popcountll(S&(Lm[i+1]|Rm[i+1]));
      if(t<best){best=t;bi=i;}}
    printf(" %d(%d/%d)",bi+1,deg,N-k); S|=1ULL<<bi;} printf("\n"); return 0;}

/* maxobj.c -- exact max over valid sequences of sum_k g(V_k, f_k) (subset DP, N <= ~24).
   usage: ./maxobj N mode [delta]
     mode 0: g = log V          (tree bound; deficit = log N! - max)
     mode 1: g = V/f            (linear "richness")
     mode 2: g = [V >= delta f] (number of rich steps)
   Prints the optimum and an optimal path with V/f at each step. Memory 2^N floats. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
int N, mode; double delta; uint64_t Lm[64], Rm[64];
static inline uint32_t valid(uint64_t S){ uint32_t v=0;
  for(int m=1;m<=N;m++){uint64_t b=1ULL<<(m-1); if(S&b)continue;
    if(__builtin_popcountll(S&Lm[m])==__builtin_popcountll(S&Rm[m])) v|=(uint32_t)b;} return v;}
static inline float g(int V,int f){ if(mode==0) return logf((float)V); if(mode==1) return (float)V/f; return V>=delta*f?1.f:0.f; }
int main(int argc,char**argv){N=atoi(argv[1]); mode=atoi(argv[2]); delta=argc>3?atof(argv[3]):0.5;
  uint64_t NS=1ULL<<N, full=NS-1;
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m; Lm[m]=Rm[m]=0;
    for(int d=1;d<=D;d++){Lm[m]|=1ULL<<(m-d-1);Rm[m]|=1ULL<<(m+d-1);}}
  float *M=malloc(NS*sizeof(float)); M[full]=0;
  for(uint64_t S=full;S-->0;){uint32_t v=valid(S); int deg=__builtin_popcount(v); float best=-1e30f;
    int f=N-__builtin_popcountll(S);
    while(v){int i=__builtin_ctz(v); v&=v-1; float t=M[S|(1ULL<<i)]; if(t>best)best=t;}
    M[S]= best<-1e29f? -1e30f : best+g(deg,f);}
  double lf=lgamma(N+1.0);
  if(mode==0) printf("N=%d deficit/N=%.4f\n",N,(lf-M[0])/N);
  else printf("N=%d mode=%d max=%.4f max/N=%.4f\n",N,mode,M[0],M[0]/N);
  uint64_t S=0; printf("path:"); for(int k=0;k<N;k++){uint32_t v=valid(S); int deg=__builtin_popcount(v); float best=-1e30f;int bi=-1;
    while(v){int i=__builtin_ctz(v); v&=v-1; float t=M[S|(1ULL<<i)]; if(t>best){best=t;bi=i;}}
    printf(" %d(%d/%d)",bi+1,deg,N-k); S|=1ULL<<bi;} printf("\n"); return 0;}

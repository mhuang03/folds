/* maxv.c -- for every s, max of V(S) over ALL sets S of size s (state bound), and over
   REACHABLE sets (sets that are the panel set of some valid prefix).  N <= ~26.
   usage: ./maxv N */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int N; uint64_t Lm[64], Rm[64];
static inline uint32_t valid(uint64_t S){ uint32_t v=0;
  for(int m=1;m<=N;m++){uint64_t b=1ULL<<(m-1); if(S&b)continue;
    if(__builtin_popcountll(S&Lm[m])==__builtin_popcountll(S&Rm[m])) v|=(uint32_t)b;} return v;}
int main(int argc,char**argv){N=atoi(argv[1]); uint64_t NS=1ULL<<N;
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m; Lm[m]=Rm[m]=0;
    for(int d=1;d<=D;d++){Lm[m]|=1ULL<<(m-d-1);Rm[m]|=1ULL<<(m+d-1);}}
  unsigned char *reach=calloc(NS,1); reach[0]=1;
  int mx[65]={0}, mr[65]={0};
  /* subsets in increasing numeric order: S|bit > S, so reachability propagates forward */
  for(uint64_t S=0;S<NS;S++){ uint32_t v=valid(S); int V=__builtin_popcount(v), s=__builtin_popcountll(S);
    if(V>mx[s]) mx[s]=V;
    if(reach[S]){ if(V>mr[s]) mr[s]=V; while(v){int i=__builtin_ctz(v); v&=v-1; reach[S|(1ULL<<i)]=1;} } }
  printf("N=%d\n s  f  maxV(all)  maxV(reachable)\n",N);
  for(int s=0;s<N;s++) printf("%2d %2d %3d %3d\n",s,N-s,mx[s],mr[s]);
  return 0;}

/* extremal.c -- exhaustive: for each s, max V(S) over all S of size s, number of maximisers,
   and the first few maximisers (as panel lists).  usage: ./extremal N [print]  (N <= 30) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int N; uint64_t Lm[64], Rm[64];
static inline uint32_t valid(uint64_t S){ uint32_t v=0;
  for(int m=1;m<=N;m++){uint64_t b=1ULL<<(m-1); if(S&b)continue;
    if(__builtin_popcountll(S&Lm[m])==__builtin_popcountll(S&Rm[m])) v|=(uint32_t)b;} return v;}
int main(int argc,char**argv){N=atoi(argv[1]); int pr=argc>2?atoi(argv[2]):0; uint64_t NS=1ULL<<N;
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m; Lm[m]=Rm[m]=0;
    for(int d=1;d<=D;d++){Lm[m]|=1ULL<<(m-d-1);Rm[m]|=1ULL<<(m+d-1);}}
  int mx[65]={0}; long cnt[65]={0};
  for(uint64_t S=0;S<NS;S++){ int s=__builtin_popcountll(S); int V=__builtin_popcount(valid(S));
    if(V>mx[s]){mx[s]=V;cnt[s]=0;} if(V==mx[s])cnt[s]++; }
  int best=0; for(int s=2;s<N;s+=2) if(mx[s]>best) best=mx[s];
  printf("N=%d ceil(2N/3)=%d max_even_s>=2=%d\n",N,(2*N+2)/3,best);
  for(int s=0;s<N;s++) printf("s=%2d maxV=%2d count=%ld\n",s,mx[s],cnt[s]);
  if(pr){ int shown[65]={0};
    for(uint64_t S=0;S<NS;S++){ int s=__builtin_popcountll(S); if(s<1||shown[s]>=pr) continue;
      uint32_t v=valid(S); if(__builtin_popcount(v)!=mx[s]) continue; shown[s]++;
      printf("s=%d S={",s); for(int i=0;i<N;i++) if(S>>i&1) printf(" %d",i+1);
      printf(" } valid={"); for(int i=0;i<N;i++) if(v>>i&1) printf(" %d",i+1); printf(" }\n"); } }
  return 0;}

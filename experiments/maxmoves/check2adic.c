/* check2adic.c -- exhaustive check of the 2-adic bound
     |S| = 2^a t (t odd, a >= 1)  ==>  (a+2) V(S) <= (a+1) N
   over all S subset [1,N], for one N (any parity).  Prints, for each a, the maximum of
   (a+2)V - (a+1)N (must be <= 0) and the max V for s = 2 mod 4 against floor(2N/3).
   usage: ./check2adic N */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int N; uint64_t Lm[64], Rm[64];
static inline int nvalid(uint64_t S){ int v=0;
  for(int m=1;m<=N;m++){uint64_t b=1ULL<<(m-1); if(S&b)continue;
    if(__builtin_popcountll(S&Lm[m])==__builtin_popcountll(S&Rm[m])) v++;} return v;}
int main(int argc,char**argv){N=atoi(argv[1]); uint64_t NS=1ULL<<N;
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m; Lm[m]=Rm[m]=0;
    for(int d=1;d<=D;d++){Lm[m]|=1ULL<<(m-d-1);Rm[m]|=1ULL<<(m+d-1);}}
  int worst[8]; for(int a=0;a<8;a++) worst[a]=-1000; int max2=0, bad=0;
  for(uint64_t S=1;S<NS;S++){ int s=__builtin_popcountll(S); if(s&1) continue;
    int a=__builtin_ctz(s); int V=nvalid(S); int d=(a+2)*V-(a+1)*N;
    if(d>worst[a]) worst[a]=d; if(d>0) bad++; if(a==1 && V>max2) max2=V; }
  printf("N=%d violations=%d  max V (s=2 mod 4)=%d floor(2N/3)=%d  worst (a+2)V-(a+1)N:",N,bad,max2,2*N/3);
  for(int a=1;a<6;a++) if(worst[a]>-1000) printf(" a=%d:%d",a,worst[a]); printf("\n"); return 0;}

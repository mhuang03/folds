/* check2adic2.c -- exhaustive check, for one N, of the 2-adic bounds
     (B)  |S| = 2^a t (t odd, a >= 1)  ==>  (a+2) V(S) <= (a+1) N
     (B') same hypothesis  ==>  2(a+2) V(S) + 2(a-1)|S| <= 2(a+1) N + a
   over all S subset [1,N].  Prints per a the maximum of (a+2)V - (a+1)N and of
   2(a+2)V + 2(a-1)s - 2(a+1)N - a (both must be <= 0), and the number of violations.
   usage: ./check2adic2 N   (N <= 30) */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int N; uint32_t Lm[64], Rm[64];
static inline int nvalid(uint32_t S){ int v=0;
  for(int m=1;m<=N;m++){uint32_t b=1u<<(m-1); if(S&b)continue;
    if(__builtin_popcount(S&Lm[m])==__builtin_popcount(S&Rm[m])) v++;} return v;}
int main(int argc,char**argv){N=atoi(argv[1]); uint64_t NS=1ULL<<N;
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m; Lm[m]=Rm[m]=0;
    for(int d=1;d<=D;d++){Lm[m]|=1u<<(m-d-1);Rm[m]|=1u<<(m+d-1);}}
  int w1[8], w2[8]; for(int a=0;a<8;a++){w1[a]=w2[a]=-100000;} long bad=0;
  for(uint64_t S=1;S<NS;S++){ int s=__builtin_popcount((uint32_t)S); if(s&1) continue;
    int a=__builtin_ctz(s); int V=nvalid((uint32_t)S);
    int d1=(a+2)*V-(a+1)*N, d2=2*(a+2)*V+2*(a-1)*s-2*(a+1)*N-a;
    if(d1>w1[a]) w1[a]=d1; if(d2>w2[a]) w2[a]=d2; if(d1>0||d2>0) bad++; }
  printf("N=%d violations=%ld ",N,bad);
  for(int a=1;a<6;a++) if(w1[a]>-100000) printf(" a=%d:(%d,%d)",a,w1[a],w2[a]); printf("\n"); return 0;}

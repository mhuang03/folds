/* parity4.c (sed-generated from parity.c): g(S) mod 4 over all subsets S of [N].
   Prints: predicted a(N) mod 16 = sum_{|S|=n} gbar(S) gbar(S^c) (even N),
   sum_{(S,m)} gbar(S) gbar(T) [m valid wrt S] (odd N), with gbar = g mod 4 in {0..3},
   and the number of sets with g odd, by size.   usage: parity4 N */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc,char**argv){
  int N=atoi(argv[1]); uint64_t full=(1ULL<<N)-1;
  uint64_t L[64],R[64];
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m;L[m]=R[m]=0;
    for(int d=1;d<=D;d++){L[m]|=1ULL<<(m-d-1);R[m]|=1ULL<<(m+d-1);}}
  uint8_t *P=calloc(full+1,1);
#define GET(s) (P[s])
  P[0]=1; uint64_t bysz[65]={0}; bysz[0]=1;
  for(uint64_t S=1;S<=full;S++){
    int b=0; uint64_t t=S;
    while(t){int i=__builtin_ctzll(t); t&=t-1; uint64_t U=S&~(1ULL<<i); int m=i+1;
      if(__builtin_popcountll(U&L[m])==__builtin_popcountll(U&R[m])) b=(b+GET(U))&3;}
    P[S]=b; if(b&1) bysz[__builtin_popcountll(S)]++;
  }
  int n=N/2; uint64_t cnt=0;
  for(uint64_t S=0;S<=full;S++){ if(__builtin_popcountll(S)!=n||!GET(S)) continue; /* mod 4 version */
    if(N%2==0){ cnt+=GET(S)*GET(full&~S); }
    else { for(int m=1;m<=N;m++){ uint64_t b=1ULL<<(m-1); if(S&b) continue;
        if(__builtin_popcountll(S&L[m])!=__builtin_popcountll(S&R[m])) continue;
        cnt+=GET(S)*GET(full&~S&~b); } } }
  printf("N=%d pred=%llu mod16=%llu  odd-by-size:",N,(unsigned long long)cnt,(unsigned long long)(cnt%16));
  for(int k=0;k<=N;k++) printf(" %llu",(unsigned long long)bysz[k]); printf("\n");
  return 0;
}

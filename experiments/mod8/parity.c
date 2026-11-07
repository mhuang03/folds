/* g(S) mod 2 over all subsets S of [N] (g = # valid orderings of S as initial steps).
   Prints: predicted a(N) mod 8 = #{S,|S|=n: g(S) g(S^c) odd} (even N),
   #{(S,m): |S|=n, m valid wrt S, g(S) g(T) odd} (odd N), and #odd sets by size.
   usage: parity N */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc,char**argv){
  int N=atoi(argv[1]); uint64_t full=(1ULL<<N)-1;
  uint64_t L[64],R[64];
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m;L[m]=R[m]=0;
    for(int d=1;d<=D;d++){L[m]|=1ULL<<(m-d-1);R[m]|=1ULL<<(m+d-1);}}
  uint8_t *P=calloc((full>>3)+1,1);
#define GET(s) ((P[(s)>>3]>>((s)&7))&1)
  P[0]=1; uint64_t bysz[65]={0}; bysz[0]=1;
  for(uint64_t S=1;S<=full;S++){
    int b=0; uint64_t t=S;
    while(t){int i=__builtin_ctzll(t); t&=t-1; uint64_t U=S&~(1ULL<<i); int m=i+1;
      if(__builtin_popcountll(U&L[m])==__builtin_popcountll(U&R[m])) b^=GET(U);}
    if(b){P[S>>3]|=1<<(S&7); bysz[__builtin_popcountll(S)]++;}
  }
  int n=N/2; uint64_t cnt=0;
  for(uint64_t S=0;S<=full;S++){ if(__builtin_popcountll(S)!=n||!GET(S)) continue;
    if(N%2==0){ if(GET(full&~S)) cnt++; }
    else { for(int m=1;m<=N;m++){ uint64_t b=1ULL<<(m-1); if(S&b) continue;
        if(__builtin_popcountll(S&L[m])!=__builtin_popcountll(S&R[m])) continue;
        if(GET(full&~S&~b)) cnt++; } } }
  printf("N=%d pred=%llu mod8=%llu  odd-by-size:",N,(unsigned long long)cnt,(unsigned long long)(cnt%8));
  for(int k=0;k<=N;k++) printf(" %llu",(unsigned long long)bysz[k]); printf("\n");
  return 0;
}

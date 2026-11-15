/* Wall models W(n,B): orderings of the left panels 1..n, windows [1,2m-1], where the panels
   to the right of n are placed by a wall that moves inwards at unit speed: before the k-th
   left panel is placed, exactly the panels p > B-k (p > n) are placed.  With S the set of
   left panels placed before m and k = |S|+1 the condition is
        |S cap [1,m-1]| = |S cap [m+1, min(n,2m-1)]| + max(0, 2m-1 - max(n, B-k)).
   W(n,2n) = H(2n), W(n,2n+1) = H(2n+1) = H(n) (hl.c), W(n,B) = H(n) for B >= 3n-1 (no wall
   panel is ever seen) and W(n,n) = H(n) (wall complete from the start; complement lemma).
   usage: wall n B      -> W(n,B)
          wall n row    -> W(n,B) for B = n .. 2n+2 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static uint64_t *g;
static uint64_t run(int n,int B){
  uint64_t full=(1ULL<<n)-1; uint64_t L[40],R[40];
  for(int m=1;m<=n;m++){ L[m]=(1ULL<<(m-1))-1; int hi=2*m-1<n?2*m-1:n; R[m]=((1ULL<<hi)-1)&~((1ULL<<m)-1); }
  memset(g,0,8*((size_t)1<<n)); g[0]=1;
  for(uint64_t S=0;S<full;S++){ uint64_t c=g[S]; if(!c)continue;
    int k=__builtin_popcountll(S)+1;
    for(int m=1;m<=n;m++){ uint64_t b=1ULL<<(m-1); if(S&b)continue;
      int mx=n>B-k?n:B-k; int ex=2*m-1-mx; if(ex<0)ex=0;
      if(__builtin_popcountll(S&L[m])==__builtin_popcountll(S&R[m])+ex) g[S|b]+=c; } }
  return g[full];
}
int main(int argc,char**argv){
  int n=atoi(argv[1]); g=malloc(8*((size_t)1<<n));
  if(!strcmp(argv[2],"row")){ for(int B=n;B<=2*n+2;B++)printf("%llu ",(unsigned long long)run(n,B)); printf("\n"); }
  else printf("%llu\n",(unsigned long long)run(n,atoi(argv[2])));
  return 0;
}

/* Half-line model H(N) through the reduction to the left half (NOTES.txt, section 2).
   H(N) = a(N; 0, infinity): panel m has window [1, min(2m-1, N)].
   Reduction [proven]: the panels m >= ceil((N+1)/2) (full windows) are forced: panel N-k is
   placed at time 2k+1.  The n = floor(N/2) left panels take the even times.  With S the set
   of left panels placed before left panel m, and k = |S|+1 (so t_m = 2k):
        |S cap [1,m-1]| = |S cap [m+1, min(n,2m-1)]| + max(0, 2m-1 - max(n, N-k)).
   usage: hl N            -> H(N)
          hl N layers     -> also the number of live sets per layer (g>0) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int main(int argc,char**argv){
  int N=atoi(argv[1]); int n=N/2; int lay=argc>2;
  uint64_t full=(1ULL<<n)-1;
  uint64_t *g=calloc((size_t)1<<n,8);
  uint64_t L[40],R[40];
  for(int m=1;m<=n;m++){ L[m]=(1ULL<<(m-1))-1; int hi=2*m-1<n?2*m-1:n; R[m]=((1ULL<<hi)-1)&~((1ULL<<m)-1); }
  g[0]=1;
  uint64_t live[64]; memset(live,0,sizeof live);
  for(uint64_t S=0;S<=full;S++){ uint64_t c=g[S]; if(!c)continue;
    int k=__builtin_popcountll(S)+1; live[k-1]++;
    if(S==full)break;
    for(int m=1;m<=n;m++){ uint64_t b=1ULL<<(m-1); if(S&b)continue;
      int mx=n>N-k?n:N-k; int ex=2*m-1-mx; if(ex<0)ex=0;
      if(__builtin_popcountll(S&L[m])==__builtin_popcountll(S&R[m])+ex) g[S|b]+=c; } }
  printf("%llu\n",(unsigned long long)g[full]);
  if(lay){ for(int k=0;k<=n;k++)printf("%llu ",(unsigned long long)live[k]); printf("\n"); }
  return 0;
}

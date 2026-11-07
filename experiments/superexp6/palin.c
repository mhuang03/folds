// mu-palindromic good class orders: odd d, mu(s) = (rho+1-s) mod* d (one fixed point f).
// pi = X f mu(rev X) is valid iff X and mu(X) are valid prefixes, X picks one element of each
// mu-pair, and f is valid after X; then mu(pi) = rev(pi) is valid automatically.
// Counts such X (DFS), for every rho.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int d,rho,f; static long cnt; static int a[64];
static int valid(uint64_t S,int m){ int r = m-1 < d-m ? m-1 : d-m; int l=0,rr=0;
  for(int k=1;k<=r;k++){ l+=(S>>(m-k))&1; rr+=(S>>(m+k))&1; } return l==rr; }
static int mu(int s){ int v=((rho+1-s)%d+d)%d; return v==0?d:v; }
static void dfs(int k,uint64_t S,uint64_t T){ // S = set(X), T = set(mu X)
  if(k==(d-1)/2){ if(valid(S,f)) cnt++; return; }
  for(int s=1;s<=d;s++){ if(s==f||((S>>s)&1)||((T>>s)&1)) continue; int t=mu(s);
    if(valid(S,s)&&valid(T,t)){ dfs(k+1,S|(1ULL<<s),T|(1ULL<<t)); if(cnt>1000000) return; } }
}
int main(int argc,char**argv){ for(d=3; d<=atoi(argv[1]); d+=2){ printf("d=%d:",d);
  for(rho=0;rho<d;rho++){ f=0; for(int s=1;s<=d;s++) if(mu(s)==s) f=s; cnt=0; dfs(0,0,0); printf(" %ld",cnt); fflush(stdout);} printf("\n"); } }

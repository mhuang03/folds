/* #midSwappable(N), N = 2n even: semi-symmetric sequences whose two middle entries
   (steps n, n+1) are mutually outside each other's windows (= the middle swap is again
   semi-symmetric).  Uses the subset DP g(S) (unsigned 128-bit) for all S, N <= ~26:
     #midSwappable = sum_{|U|=n-1} g(U) sum_{x,y} [x ok|U][y ok|U+x][x,y independent] g(rest)
   (completions of a prefix set A are counted by g([N] \ A), complement lemma).
   usage: midswap N */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static void pr(u128 v){char b[64];int q=63;b[q]=0;if(!v)b[--q]='0';while(v){b[--q]='0'+(int)(v%10);v/=10;}printf("%s",b+q);}
int main(int argc,char**argv){
  int N=atoi(argv[1]); int n=N/2; uint64_t full=(1ULL<<N)-1;
  uint64_t L[64],R[64]; int rad[64];
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m;rad[m]=D;L[m]=R[m]=0;
    for(int d=1;d<=D;d++){L[m]|=1ULL<<(m-d-1);R[m]|=1ULL<<(m+d-1);}}
  u128 *g=calloc(full+1,sizeof(u128)); g[0]=1;
#define OK(U,m) (__builtin_popcountll((U)&L[m])==__builtin_popcountll((U)&R[m]))
  for(uint64_t S=1;S<=full;S++){ u128 s=0; uint64_t t=S;
    while(t){int i=__builtin_ctzll(t); t&=t-1; uint64_t U=S&~(1ULL<<i); if(OK(U,i+1)) s+=g[U];}
    g[S]=s; }
  u128 cnt=0;
  for(uint64_t U=0;U<=full;U++){ if(__builtin_popcountll(U)!=n-1||!g[U]) continue;
    for(int x=1;x<=N;x++){ uint64_t bx=1ULL<<(x-1); if(U&bx||!OK(U,x)) continue;
      for(int y=1;y<=N;y++){ uint64_t by=1ULL<<(y-1); if((U|bx)&by||!OK(U|bx,y)) continue;
        int d=x>y?x-y:y-x; if(d<=rad[x]||d<=rad[y]) continue; /* not independent */
        cnt+=g[U]*g[full&~(U|bx|by)]; } } }
  printf("%d a=",N); pr(g[full]); printf(" midSwappable="); pr(cnt);
  printf("  mod8=%d\n",(int)(cnt%8));
  return 0;
}

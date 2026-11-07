// P(d,b): is there a sequence pi of [d] valid in the d-strip such that rot_b(pi) is also
// valid?  (rot_b(s) = (s - 1 + b) mod d + 1.)  Equivalent to the existence of a good class
// order for the generalised composition (residue classes mod d of the N-strip, N = dm + rho,
// with b = d - rho or rho; see PROOFS.txt section 3).  DFS with a failed-state cache.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int d,b; static int a[64];
static int valid(uint64_t S,int m){ int r = m-1 < d-m ? m-1 : d-m; int l=0,rr=0;
  for(int k=1;k<=r;k++){ l+=(S>>(m-k))&1; rr+=(S>>(m+k))&1; } return l==rr; }
static int rot(int s){ return (s-1+b)%d+1; }
#define HB 24
static uint64_t *H; static long nodes;
static int seen(uint64_t S){ uint64_t h=S*0x9E3779B97F4A7C15ULL; h>>= (64-HB); for(int i=0;i<8;i++){ uint64_t v=H[(h+i)&((1<<HB)-1)]; if(v==S+1) return 1; if(v==0) return 0; } return 0; }
static void mark(uint64_t S){ uint64_t h=S*0x9E3779B97F4A7C15ULL; h>>= (64-HB); for(int i=0;i<8;i++){ uint64_t *p=&H[(h+i)&((1<<HB)-1)]; if(*p==0){*p=S+1;return;} } H[h]=S+1; }
static int dfs(int k,uint64_t S,uint64_t T){
  if(k==d) return 1; if(seen(S)) return 0; nodes++; if(nodes>200000000L) return 0;
  for(int s=1;s<=d;s++){ if((S>>s)&1) continue; int t=rot(s);
    if(valid(S,s)&&valid(T,t)){ a[k]=s; if(dfs(k+1,S|(1ULL<<s),T|(1ULL<<t))) return 1; } }
  mark(S); return 0;
}
int main(int argc,char**argv){ int lo=atoi(argv[1]),hi=atoi(argv[2]); H=calloc(1<<HB,8);
  for(d=lo; d<=hi; d+=2){ printf("d=%d:",d); fflush(stdout);
    for(b=1;b<d;b++){ memset(H,0,(size_t)8<<HB); nodes=0; int ok=dfs(0,0,0); printf(" %c",ok?'Y':(nodes>200000000L?'?':'N')); fflush(stdout); }
    printf("\n"); } }

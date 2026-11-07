// csolve.c qlo qhi : for odd q in [qlo, qhi] and every even nu = 2w < q, is the odd
// near-reduction (PROOFS.txt Theorem R) applicable, i.e. are
//   C(m+1, w, w+1) and C(m, w, w)   (q = 2m+1)
// solvable?  C(n, w, c) = GoodL(n, w mod n) orders with "i before md(2i - c, n)" for 2i <= c.
// Also checks the composed order directly against GoodL(q, 2w).  Output: one line per q,
// characters Y (both solvable and composed order verified), N (some C unsolvable), ? (budget).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int n,nu; static uint64_t Lm[70],Rm[70]; static int sg[70]; static uint64_t need[70];
static inline int val(uint64_t S,int t){ return __builtin_popcountll(S&Lm[t])==__builtin_popcountll(S&Rm[t]); }
#define HB 24
static uint64_t *H; static long nodes,budget=50000000L;
static int seen(uint64_t S){ uint64_t h=(S*0x9E3779B97F4A7C15ULL)>>(64-HB); for(int i=0;i<8;i++){ uint64_t v=H[(h+i)&((1<<HB)-1)]; if(v==S+1) return 1; if(v==0) return 0; } return 0; }
static void mark(uint64_t S){ uint64_t h=(S*0x9E3779B97F4A7C15ULL)>>(64-HB); for(int i=0;i<8;i++){ uint64_t *p=&H[(h+i)&((1<<HB)-1)]; if(*p==0){*p=S+1;return;} } H[h]=S+1; }
static int a[70];
static int dfs(int k,uint64_t S,uint64_t T){ if(k==n) return 1; if(seen(S)) return 0; if(++nodes>budget) return 0;
  for(int t=1;t<=n;t++){ if(S>>t&1) continue; if((need[t]&S)!=need[t]) continue; int u=sg[t];
    if(val(S,t)&&val(T,u)){ a[k]=t; if(dfs(k+1,S|1ULL<<t,T|1ULL<<u)) return 1; } }
  mark(S); return 0; }
static void setup(int nn,int w,int c){ n=nn; nu=w%n;
  for(int t=1;t<=n;t++){ int r=t-1<n-t?t-1:n-t; Lm[t]=Rm[t]=0; for(int j=1;j<=r;j++){Lm[t]|=1ULL<<(t-j);Rm[t]|=1ULL<<(t+j);} sg[t]=((nu-t)%n+n)%n+1; need[t]=0; }
  for(int i=1;2*i<=c&&i<=n;i++){ int p=((2*i-c-1)%n+n)%n+1; if(p!=i) need[p]|=1ULL<<i; } }
static int solve(int nn,int w,int c,int *out){ setup(nn,w,c); memset(H,0,(size_t)8<<HB); nodes=0; int ok=dfs(0,0,0); if(ok) memcpy(out,a,sizeof(int)*nn); return ok?1:(nodes>budget?2:0); }
// direct GoodL check of an order of [q]
static int goodq(int q,int v,int *p){ uint64_t L[70],R[70]; int s[70]; for(int t=1;t<=q;t++){ int r=t-1<q-t?t-1:q-t; L[t]=R[t]=0; for(int j=1;j<=r;j++){L[t]|=1ULL<<(t-j);R[t]|=1ULL<<(t+j);} s[t]=((v-t)%q+q)%q+1; }
  uint64_t S=0,T=0; for(int k=0;k<q;k++){ int t=p[k],u=s[t]; if(__builtin_popcountll(S&L[t])!=__builtin_popcountll(S&R[t])) return 0; if(__builtin_popcountll(T&L[u])!=__builtin_popcountll(T&R[u])) return 0; S|=1ULL<<t; T|=1ULL<<u; } return 1; }
int main(int argc,char**argv){ int lo=atoi(argv[1]),hi=atoi(argv[2]); if(argc>3) budget=atol(argv[3]); H=calloc(1<<HB,8);
  for(int q=lo|1;q<=hi;q+=2){ int m=(q-1)/2; printf("q=%d:",q); fflush(stdout);
    for(int w=1;2*w<q;w++){ int A[70],B[70],P[70]; int r1=solve(m+1,w,w+1,A); int r2=r1==1?solve(m,w,w,B):0;
      char ch; if(r1==1&&r2==1){ for(int k=0;k<=m;k++) P[k]=2*A[k]-1; for(int k=0;k<m;k++) P[m+1+k]=2*B[m-1-k]; ch=goodq(q,2*w,P)?'Y':'!'; }
      else ch=(r1==2||r2==2)?'?':'N';
      printf(" %d%c",2*w,ch); fflush(stdout); }
    printf("\n"); }
}

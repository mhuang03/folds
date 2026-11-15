/* weak.c: count valid weak orders (ordered set partitions) of [N] by number of blocks.
 *
 *   ./weak N conv kind
 *     conv = a : each m in B_i balanced w.r.t. S = B_1 u ... u B_{i-1}
 *            b : (a) and also balanced w.r.t. S u B_i \ {m}
 *            c : every linear refinement of the weak order is a valid sequence
 *                (= (a) and no element of B_i lies in the window of another element of B_i)
 *            d : some linear refinement is a valid sequence
 *     kind = semi (semi-symmetric) | sym (symmetric, 3-AP-free)
 *
 * A weak order is a chain 0 = S_0 < S_1 < ... < S_k = [N]; validity of each link depends only
 * on (S_{i-1}, S_i).  f[S][k] = number of valid chains from 0 to S with k links.
 * Output line:  N conv kind  W(N,1) ... W(N,N)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
typedef uint32_t u32;

static int N; static u32 FULL;
static u32 *bal;           /* bal[S] = mask of m (bit m-1) balanced / symmetric w.r.t. S \ {m} */

static void print128(u128 x){ char b[50]; int i=49; b[i]=0; if(!x) b[--i]='0'; while(x){ b[--i]='0'+(int)(x%10); x/=10;} printf("%s", b+i); }

int main(int argc, char **argv){
  if(argc<4){ fprintf(stderr,"usage: weak N conv(a|b|c|d) kind(semi|sym)\n"); return 1; }
  N=atoi(argv[1]); char conv=argv[2][0]; int sym = !strcmp(argv[3],"sym");
  FULL = (N==32)?0xffffffffu:((1u<<N)-1);
  size_t M = (size_t)1<<N;
  bal = malloc(M*sizeof(u32));
  /* window masks */
  u32 L[32], R[32], win[32];
  for(int m=1;m<=N;m++){ int r = (m-1 < N-m)? m-1 : N-m; L[m-1]=R[m-1]=0;
    for(int d=1;d<=r;d++){ L[m-1] |= 1u<<(m-d-1); R[m-1] |= 1u<<(m+d-1);} win[m-1]=L[m-1]|R[m-1]; }
  for(size_t S=0;S<M;S++){ u32 b=0;
    for(int i=0;i<N;i++){
      if(!sym){ if(__builtin_popcount(S&L[i])==__builtin_popcount(S&R[i])) b|=1u<<i; }
      else { int ok=1; int m=i+1; int r=(m-1<N-m)?m-1:N-m;
        for(int d=1;d<=r&&ok;d++) if( ((S>>(m-d-1))&1) != ((S>>(m+d-1))&1) ) ok=0;
        if(ok) b|=1u<<i; }
    }
    bal[S]=b; }
  /* adjacency for conv c: m ~ m' iff one lies in the window of the other */
  u32 adj[32]; for(int i=0;i<N;i++){ adj[i]=win[i]; } for(int i=0;i<N;i++) for(int j=0;j<N;j++) if((win[i]>>j)&1) adj[j]|=1u<<i;
  unsigned char *indep=NULL;
  if(conv=='c'){ indep=malloc(M); indep[0]=1; for(size_t B=1;B<M;B++){ int i=__builtin_ctz(B); size_t B2=B&(B-1); indep[B]= indep[B2] && !(adj[i]&B2); } }
  unsigned char *r=NULL; if(conv=='d'){ r=calloc(M,1); }
  int K=N+1;
  u128 *f = calloc(M*(size_t)K, sizeof(u128));
  f[0]=1; /* f[S*K+k] */
  for(size_t S=0;S<M-1;S++){
    u128 *fs=f+S*K; int ps=__builtin_popcount(S);
    int any=0; for(int k=0;k<=ps;k++) if(fs[k]) {any=1;break;}
    if(!any) continue;
    if(conv=='d'){
      u32 comp = FULL & ~(u32)S;
      r[0]=1;
      for(u32 B=(0-comp)&comp; ; B=(B-comp)&comp){
        if(!B) break;
        int ok=0; u32 t=B;
        while(t){ int i=__builtin_ctz(t); t&=t-1; u32 B2=B^(1u<<i);
          if(r[B2] && ((bal[S|B2]>>i)&1)) { ok=1; break; } }
        r[B]=ok;
        if(ok){ u128 *ft=f+((size_t)S|B)*K; for(int k=0;k<=ps;k++) ft[k+1]+=fs[k]; }
      }
    } else {
      u32 av = bal[S] & ~(u32)S & FULL;
      for(u32 B=av; B; B=(B-1)&av){
        if(conv=='b' && (B & ~bal[S|B])) continue;
        if(conv=='c' && !indep[B]) continue;
        u128 *ft=f+((size_t)S|B)*K; for(int k=0;k<=ps;k++) ft[k+1]+=fs[k];
      }
    }
  }
  printf("%d %c %s", N, conv, sym?"sym":"semi");
  for(int k=1;k<=N;k++){ printf(" "); print128(f[(M-1)*K+k]); }
  printf("\n");
  return 0;
}

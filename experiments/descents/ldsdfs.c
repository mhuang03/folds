/* Search for a valid sequence on [1..N] whose longest DECREASING subsequence has length <= L.
   (By mirror symmetry this is the same as LIS <= L.)  DFS over valid prefixes with
   - completability pruning (comp[S]: some valid completion of S exists),
   - patience state t[1..L]: t[i] = max last value of a decreasing subsequence of length i,
   - a hash set of dead states (S, t).
   usage: ldsdfs N L.  Prints a sequence or "none". */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int N, L; static uint32_t Lm[40], Rm[40]; static unsigned char *comp;
typedef struct { uint32_t S; uint32_t t; } key_t2;
static uint64_t *tab; static size_t cap, used;
static uint64_t hsh(uint64_t x){ x^=x>>33; x*=0xff51afd7ed558ccdULL; x^=x>>33; x*=0xc4ceb9fe1a85ec53ULL; x^=x>>33; return x; }
static int dead(uint64_t k){ size_t i=hsh(k)&(cap-1); while(tab[i]){ if(tab[i]==k) return 1; i=(i+1)&(cap-1);} return 0; }
static void mark(uint64_t k){ if(used*10>cap*7) return; size_t i=hsh(k)&(cap-1); while(tab[i]){ if(tab[i]==k) return; i=(i+1)&(cap-1);} tab[i]=k; used++; }
static int valid(uint32_t S,int m){ return __builtin_popcount(S&Lm[m])==__builtin_popcount(S&Rm[m]); }
static int seq[40];
static int rec(uint32_t S, int depth, int *t){
  if(depth==N) return 1;
  uint64_t key=S; for(int i=0;i<L;i++) key = key*37 + t[i]; key ^= (uint64_t)1<<63;
  if(dead(key)) return 0;
  for(int m=1;m<=N;m++){
    if(S>>(m-1)&1) continue; if(!valid(S,m)) continue; uint32_t T=S|(1u<<(m-1)); if(!comp[T]) continue;
    /* extend: largest i with t[i] > m  (t[i]=0 means empty) */
    int i=0; while(i<L && t[i]>m) i++;
    if(i>=L) continue;           /* would create decreasing subsequence of length L+1 */
    int nt[8]; memcpy(nt,t,sizeof(int)*L); if(m>nt[i]) nt[i]=m;
    seq[depth]=m; if(rec(T,depth+1,nt)) return 1; }
  mark(key); return 0; }
int main(int argc,char**argv){ N=atoi(argv[1]); L=atoi(argv[2]);
  for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m; for(int d=1;d<=r;d++){Lm[m]|=1u<<(m-d-1); Rm[m]|=1u<<(m+d-1);} }
  uint32_t F=(N==32)?0xffffffffu:((1u<<N)-1); comp=calloc((size_t)F+1,1); comp[F]=1;
  for(int64_t S=F;S>=0;S--){ if(comp[S]) continue; for(int m=1;m<=N;m++) if(!(S>>(m-1)&1)&&valid((uint32_t)S,m)&&comp[S|(1u<<(m-1))]){comp[S]=1;break;} }
  cap=1ULL<<27; tab=calloc(cap,8);
  int t[8]={0};
  if(rec(0,0,t)){ printf("N=%d L=%d found:",N,L); for(int i=0;i<N;i++) printf(" %d",seq[i]); printf("\n"); }
  else printf("N=%d L=%d none (dead states %zu)\n",N,L,used);
  return 0; }

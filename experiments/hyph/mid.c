// mid.c q nu [k] : forward reachability over subsets for GoodL q nu (pi valid and sig o pi
// valid, sig(t) = ((nu - t) mod q) + 1).  Prints the number of reachable sets per size, and the
// "middle" sets of size k (reachable with reachable complement).  Bit t-1 = panel t.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int q,nu; static uint32_t Lm[64],Rm[64]; static int sg[64];
static inline int val(uint32_t S,int m){ return __builtin_popcount(S&Lm[m])==__builtin_popcount(S&Rm[m]); }
static uint32_t sgs(uint32_t S){ uint32_t T=0; for(int t=1;t<=q;t++) if(S>>(t-1)&1) T|=1u<<(sg[t]-1); return T; }
int main(int c,char**v){ q=atoi(v[1]); nu=atoi(v[2]); int k=c>3?atoi(v[3]):-1;
  for(int m=1;m<=q;m++){ int r=m-1<q-m?m-1:q-m; Lm[m]=Rm[m]=0; for(int j=1;j<=r;j++){Lm[m]|=1u<<(m-j-1);Rm[m]|=1u<<(m+j-1);} sg[m]=((nu-m)%q+q)%q+1; }
  uint32_t full=(uint32_t)((1ull<<q)-1); uint8_t *F=calloc(((size_t)1<<q)/8+1,1);
  #define G(S) ((F[(S)>>3]>>((S)&7))&1)
  #define P(S) (F[(S)>>3]|=1<<((S)&7))
  P(0); long cnt[64]={0};
  for(uint64_t S=0;S<=full;S++){ if(!G(S)) continue; cnt[__builtin_popcount(S)]++; uint32_t T=sgs(S);
    for(int m=1;m<=q;m++){ if(S>>(m-1)&1) continue; if(val(S,m)&&val(T,sg[m])) P(S|(1u<<(m-1))); } }
  printf("q=%d nu=%d full=%d\n",q,nu,G(full)); for(int i=0;i<=q;i++) printf("%ld ",cnt[i]); printf("\n");
  if(k>=0){ long n=0; for(uint64_t S=0;S<=full;S++) if(__builtin_popcount(S)==k&&G(S)&&G(full^S)){ n++; if(n<=200){ for(int t=1;t<=q;t++) if(S>>(t-1)&1) printf("%d ",t); printf("\n");} } printf("middle %ld\n",n); }
}

// dsb.c q [print] : double self-balanced splits.  X subset of [q] is SB for nu if every x in X has
// X balanced around x in the q-strip AND sig(X) balanced around sig(x) (sig = sig_{q,nu}).
// A 2-block split is X with X and its complement both SB.  Prints, per nu, the sizes of the
// splits (and the sets with print=1).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int q,nu; static uint32_t Lm[64],Rm[64]; static int sg[64];
static inline int val(uint32_t S,int m){ return __builtin_popcount(S&Lm[m])==__builtin_popcount(S&Rm[m]); }
static uint32_t sgs(uint32_t S){ uint32_t T=0; for(int t=1;t<=q;t++) if(S>>(t-1)&1) T|=1u<<(sg[t]-1); return T; }
static int sb(uint32_t S){ uint32_t T=sgs(S); for(int t=1;t<=q;t++) if(S>>(t-1)&1){ if(!val(S,t)||!val(T,sg[t])) return 0; } return 1; }
int main(int c,char**v){ q=atoi(v[1]); int pr=c>2?atoi(v[2]):0; uint32_t full=(uint32_t)((1ull<<q)-1);
  for(int m=1;m<=q;m++){ int r=m-1<q-m?m-1:q-m; Lm[m]=Rm[m]=0; for(int j=1;j<=r;j++){Lm[m]|=1u<<(m-j-1);Rm[m]|=1u<<(m+j-1);} }
  for(nu=0;nu<q;nu++){ for(int m=1;m<=q;m++) sg[m]=((nu-m)%q+q)%q+1;
    long cnt[64]={0};
    for(uint32_t S=1;S<full;S++){ if(!(S&1)) continue; if(sb(S)&&sb(full^S)){ cnt[__builtin_popcount(S)]++;
        if(pr){ printf(" nu=%d X=",nu); for(int t=1;t<=q;t++) if(S>>(t-1)&1) printf("%d,",t); printf("\n"); } } }
    printf("q=%d nu=%d:",q,nu); for(int i=1;i<q;i++) if(cnt[i]) printf(" %d:%ld",i,cnt[i]); printf("\n"); }
}

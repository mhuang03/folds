// clsblk.c q : for every nu and modulus m (2 <= m < q), the blocks = residue classes mod m of the
// q-strip (strip-1 coordinates).  Report whether every block is double self-balanced (SB in the
// q-strip and its sig-image SB) and whether some block order satisfies the cross condition
// (union of earlier blocks balanced around each point of the current block, in both strips).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int q,nu,m; static uint32_t Lm[64],Rm[64]; static int sg[64]; static uint32_t B[64]; static int nb;
static inline int val(uint32_t S,int t){ return __builtin_popcount(S&Lm[t])==__builtin_popcount(S&Rm[t]); }
static uint32_t sgs(uint32_t S){ uint32_t T=0; for(int t=1;t<=q;t++) if(S>>(t-1)&1) T|=1u<<(sg[t]-1); return T; }
static int sbrel(uint32_t S,uint32_t X){ // S balanced around every x in X, both strips (S excludes x)
  uint32_t T=sgs(S); for(int t=1;t<=q;t++) if(X>>(t-1)&1){ if(!val(S&~(1u<<(t-1)),t)||!val(T&~(1u<<(sg[t]-1)),sg[t])) return 0; } return 1; }
static int ord[64];
static int dfs(int k,uint32_t S,uint32_t used){ if(k==nb) return 1;
  for(int i=0;i<nb;i++){ if(used>>i&1) continue; if(sbrel(S,B[i])){ ord[k]=i; if(dfs(k+1,S|B[i],used|1u<<i)) return 1; } } return 0; }
int main(int c,char**v){ q=atoi(v[1]);
  for(int t=1;t<=q;t++){ int r=t-1<q-t?t-1:q-t; Lm[t]=Rm[t]=0; for(int j=1;j<=r;j++){Lm[t]|=1u<<(t-j-1);Rm[t]|=1u<<(t+j-1);} }
  for(nu=0;nu<q;nu++){ for(int t=1;t<=q;t++) sg[t]=((nu-t)%q+q)%q+1; printf("nu=%d:",nu);
    for(m=2;m<q;m++){ nb=m; for(int i=0;i<m;i++){ B[i]=0; for(int t=i+1;t<=q;t+=m) B[i]|=1u<<(t-1); }
      int allsb=1; for(int i=0;i<m;i++) if(!sbrel(B[i],B[i])) allsb=0;
      if(allsb && dfs(0,0,0)) printf(" m=%d",m); }
    printf("\n"); }
}

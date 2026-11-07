// apmid.c q kmin : for each nu, the cyclic arithmetic progressions (a, a+d, ..., length k) that
// are middle sets of GoodL q nu (prefix of some good order).  Prints (k, d, a) lists.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int q,nu; static uint32_t Lm[64],Rm[64]; static int sg[64];
static inline int val(uint32_t S,int m){ return __builtin_popcount(S&Lm[m])==__builtin_popcount(S&Rm[m]); }
static uint32_t sgs(uint32_t S){ uint32_t T=0; for(int t=1;t<=q;t++) if(S>>(t-1)&1) T|=1u<<(sg[t]-1); return T; }
int main(int c,char**v){ q=atoi(v[1]); int kmin=atoi(v[2]);
  uint32_t full=(uint32_t)((1ull<<q)-1); uint8_t *F=malloc(((size_t)1<<q)/8+1);
  #define G(S) ((F[(S)>>3]>>((S)&7))&1)
  #define P(S) (F[(S)>>3]|=1<<((S)&7))
  for(nu=0;nu<q;nu++){
  for(int m=1;m<=q;m++){ int r=m-1<q-m?m-1:q-m; Lm[m]=Rm[m]=0; for(int j=1;j<=r;j++){Lm[m]|=1u<<(m-j-1);Rm[m]|=1u<<(m+j-1);} sg[m]=((nu-m)%q+q)%q+1; }
  for(size_t i=0;i<((size_t)1<<q)/8+1;i++)F[i]=0;
  P(0);
  for(uint64_t S=0;S<=full;S++){ if(!G(S)) continue; uint32_t T=sgs(S);
    for(int m=1;m<=q;m++){ if(S>>(m-1)&1) continue; if(val(S,m)&&val(T,sg[m])) P(S|(1u<<(m-1))); } }
  printf("nu=%d:",nu);
  for(int k=kmin;k<=q-kmin;k++) for(int d=2;d<=q/2;d++) for(int a=1;a<=q;a++){ uint32_t S=0; for(int j=0;j<k;j++) S|=1u<<(((a-1+j*d)%q));
     if(G(S)&&G(full^S)) printf(" (%d,%d,%d)",k,d,a); }
  printf("\n"); }
}

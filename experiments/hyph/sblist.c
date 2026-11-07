// sblist.c q nu kmin : list the double self-balanced sets X (|X| >= kmin) for (q, nu).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int q,nu; static uint32_t Lm[64],Rm[64]; static int sg[64];
static inline int val(uint32_t S,int m){ return __builtin_popcount(S&Lm[m])==__builtin_popcount(S&Rm[m]); }
static uint32_t sgs(uint32_t S){ uint32_t T=0; for(int t=1;t<=q;t++) if(S>>(t-1)&1) T|=1u<<(sg[t]-1); return T; }
static int sb(uint32_t S){ uint32_t T=sgs(S); for(int t=1;t<=q;t++) if(S>>(t-1)&1){ if(!val(S,t)||!val(T,sg[t])) return 0; } return 1; }
int main(int c,char**v){ q=atoi(v[1]); nu=atoi(v[2]); int kmin=atoi(v[3]); uint32_t full=(uint32_t)((1ull<<q)-1);
  for(int m=1;m<=q;m++){ int r=m-1<q-m?m-1:q-m; Lm[m]=Rm[m]=0; for(int j=1;j<=r;j++){Lm[m]|=1u<<(m-j-1);Rm[m]|=1u<<(m+j-1);} sg[m]=((nu-m)%q+q)%q+1; }
  long cnt[64]={0};
  for(uint32_t S=1;S<=full;S++){ int k=__builtin_popcount(S); if(k<kmin) continue; if(sb(S)){ cnt[k]++; for(int t=1;t<=q;t++) if(S>>(t-1)&1) printf("%d ",t); printf("\n"); } }
  for(int i=1;i<=q;i++) if(cnt[i]) printf(" %d:%ld",i,cnt[i]); printf("\n");
}

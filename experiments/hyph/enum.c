// enum.c q nu [maxprint] : enumerate all GoodL q nu orders (DFS with dead-state cache) and print
// those with the fewest "breaks" (positions where the consecutive difference mod q changes).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int q,nu; static uint32_t Lm[64],Rm[64]; static int sg[64];
static inline int val(uint32_t S,int t){ return __builtin_popcount(S&Lm[t])==__builtin_popcount(S&Rm[t]); }
static uint8_t *dead; static int a[64]; static long nsol; static int best=99; static int maxp;
static void report(){ int br=0; for(int i=2;i<q;i++){ int d1=((a[i-1]-a[i-2])%q+q)%q, d2=((a[i]-a[i-1])%q+q)%q; if(d1!=d2) br++; }
  nsol++; if(br<best){ best=br; } if(br<=maxp){ printf("br=%d:",br); for(int i=0;i<q;i++) printf(" %d",a[i]); printf("\n"); } }
static int dfs(int k,uint32_t S,uint32_t T){ if(k==q){ report(); return 1; } if(dead[S]) return 0; int any=0;
  for(int t=1;t<=q;t++){ if(S>>(t-1)&1) continue; if(val(S,t)&&val(T,sg[t])){ a[k]=t; if(dfs(k+1,S|1u<<(t-1),T|1u<<(sg[t]-1))) any=1; } }
  if(!any) dead[S]=1; return any; }
int main(int c,char**v){ q=atoi(v[1]); nu=atoi(v[2]); maxp=c>3?atoi(v[3]):2;
  for(int t=1;t<=q;t++){ int r=t-1<q-t?t-1:q-t; Lm[t]=Rm[t]=0; for(int j=1;j<=r;j++){Lm[t]|=1u<<(t-j-1);Rm[t]|=1u<<(t+j-1);} sg[t]=((nu-t)%q+q)%q+1; }
  dead=calloc((size_t)1<<q,1); dfs(0,0,0); printf("q=%d nu=%d solutions=%ld minbreaks=%d\n",q,nu,nsol,best);
}

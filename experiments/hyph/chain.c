// chain.c q nu kmin : BFS for a chain decomposition of [q] into double self-balanced blocks of
// size >= kmin (each block B: (S u B) - b balanced around b for all b in B, both strips, where S =
// union of the earlier blocks; equivalently B SB and S balanced around B).  Prints the minimum
// number of blocks and one optimal chain.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int q,nu; static uint32_t Lm[64],Rm[64]; static int sg[64];
static inline int val(uint32_t S,int t){ return __builtin_popcount(S&Lm[t])==__builtin_popcount(S&Rm[t]); }
static uint32_t sgs(uint32_t S){ uint32_t T=0; for(int t=1;t<=q;t++) if(S>>(t-1)&1) T|=1u<<(sg[t]-1); return T; }
static int rel(uint32_t S,uint32_t X){ uint32_t T=sgs(S); for(int t=1;t<=q;t++) if(X>>(t-1)&1){ if(!val(S&~(1u<<(t-1)),t)||!val(T&~(1u<<(sg[t]-1)),sg[t])) return 0; } return 1; }
int main(int c,char**v){ q=atoi(v[1]); nu=atoi(v[2]); int kmin=atoi(v[3]); uint32_t full=(uint32_t)((1ull<<q)-1);
  for(int t=1;t<=q;t++){ int r=t-1<q-t?t-1:q-t; Lm[t]=Rm[t]=0; for(int j=1;j<=r;j++){Lm[t]|=1u<<(t-j-1);Rm[t]|=1u<<(t+j-1);} sg[t]=((nu-t)%q+q)%q+1; }
  int cap=1<<20; uint32_t *bl=malloc(cap*4); int nbl=0;
  for(uint32_t S=1;S<full;S++){ if(__builtin_popcount(S)<kmin) continue; if(rel(S,S)){ if(nbl<cap) bl[nbl++]=S; } }
  uint8_t *d=malloc((size_t)1<<q); uint32_t *par=calloc((size_t)1<<q,4); for(size_t i=0;i<((size_t)1<<q);i++) d[i]=255; d[0]=0;
  uint32_t *cur=malloc(4*(1<<22)),*nxt=malloc(4*(1<<22)); int nc=1,nn; cur[0]=0; int lev=0;
  while(nc&&d[full]==255){ nn=0; for(int i=0;i<nc;i++){ uint32_t S=cur[i]; for(int j=0;j<nbl;j++){ uint32_t B=bl[j]; if(B&S) continue; uint32_t U=S|B; if(d[U]!=255) continue; if(rel(U,B)){ d[U]=lev+1; par[U]=S; if(nn<(1<<22)) nxt[nn++]=U; } } }
    uint32_t*t=cur;cur=nxt;nxt=t;nc=nn;lev++; }
  printf("q=%d nu=%d kmin=%d blocks(SB)=%d min=%d:",q,nu,kmin,nbl,d[full]==255?-1:d[full]);
  if(d[full]!=255){ uint32_t U=full; while(U){ uint32_t S=par[U],B=U^S; printf(" {"); for(int t=1;t<=q;t++) if(B>>(t-1)&1) printf("%d,",t); printf("}"); U=S; } }
  printf("\n");
}

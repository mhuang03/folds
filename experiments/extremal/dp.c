/* Subset DP for extremal statistics of semi-symmetric fold sequences.
   usage: dp N   prints max free, max lrmax, min des and one optimal sequence for each.
   Bit (m-1) of a mask <-> panel m.  1 core, memory ~ 2^N * (N+3) bytes. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int N; static uint32_t Lm[40], Rm[40];
static inline int valid(uint32_t S, int m){ return __builtin_popcount(S&Lm[m])==__builtin_popcount(S&Rm[m]); }
static inline int isfree(uint32_t S,int m){ return ((Lm[m]|Rm[m])&S)==0; }
int main(int argc,char**argv){
  N=atoi(argv[1]); uint32_t FULL=(N==32)?0xffffffffu:((1u<<N)-1);
  for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m; Lm[m]=Rm[m]=0;
    for(int d=1;d<=r;d++){Lm[m]|=1u<<(m-d-1); Rm[m]|=1u<<(m+d-1);} }
  size_t T=(size_t)1<<N;
  signed char *fr=malloc(T), *lr=malloc(T); signed char *ds=malloc(T*(size_t)(N+1));
  memset(fr,-1,T); memset(lr,-1,T); memset(ds,127,T*(size_t)(N+1));
  fr[0]=0; lr[0]=0; ds[0]=0; /* last=0 means none */
  for(size_t S=0;S<T;S++){ if(fr[S]<0) continue;
    int mx = S? 32-__builtin_clz((uint32_t)S):0;
    for(int m=1;m<=N;m++){ if(S>>(m-1)&1) continue; if(!valid(S,m)) continue;
      size_t S2=S|(1u<<(m-1));
      int f=fr[S]+isfree(S,m); if(f>fr[S2]) fr[S2]=f;
      int l=lr[S]+(m>mx); if(l>lr[S2]) lr[S2]=l;
      for(int last=0;last<=N;last++){ int v=ds[S*(N+1)+last]; if(v==127) continue;
        int w=v+(last>m); if(w<ds[S2*(N+1)+m]) ds[S2*(N+1)+m]=w; }
    }
  }
  int best=127,bl=0; for(int l=1;l<=N;l++) if(ds[FULL*(size_t)(N+1)+l]<best){best=ds[FULL*(size_t)(N+1)+l];bl=l;}
  printf("N=%d maxfree=%d maxlr=%d mindes=%d  App(N-1)=%d\n",N,fr[FULL],lr[FULL],best,fr[FULL^(1u<<(N-1))]);
  int seq[40];
  { uint32_t S=FULL; for(int k=N-1;k>=0;k--){ for(int m=1;m<=N;m++){ if(!(S>>(m-1)&1)) continue; uint32_t P=S&~(1u<<(m-1));
        if(fr[P]>=0 && valid(P,m) && fr[P]+isfree(P,m)==fr[S]){seq[k]=m;S=P;break;} } }
    printf(" free:"); for(int k=0;k<N;k++){ uint32_t P=0; for(int j=0;j<k;j++)P|=1u<<(seq[j]-1); printf(" %d%s",seq[k],isfree(P,seq[k])?"*":"");} printf("\n"); }
  { uint32_t S=FULL; for(int k=N-1;k>=0;k--){ for(int m=1;m<=N;m++){ if(!(S>>(m-1)&1)) continue; uint32_t P=S&~(1u<<(m-1));
        int mx=P?32-__builtin_clz(P):0;
        if(lr[P]>=0 && valid(P,m) && lr[P]+(m>mx)==lr[S]){seq[k]=m;S=P;break;} } }
    printf(" lr:"); for(int k=0;k<N;k++) printf(" %d",seq[k]); printf("\n"); }
  { uint32_t S=FULL; int cur=bl, cv=best; for(int k=N-1;k>=0;k--){ seq[k]=cur; uint32_t P=S&~(1u<<(cur-1));
      int found=0; for(int last=0;last<=N && !found;last++){ int v=ds[P*(size_t)(N+1)+last]; if(v==127) continue;
        if(valid(P,cur) && v+(last>cur)==cv){ S=P; cv=v; cur=last; found=1;} } }
    printf(" des:"); for(int k=0;k<N;k++) printf(" %d%s",seq[k],(k+1<N&&seq[k]>seq[k+1])?" |":""); printf("\n"); }
  return 0; }

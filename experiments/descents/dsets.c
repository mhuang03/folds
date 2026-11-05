/* D(S) = min #runs of a valid ordering of S (prefix of a valid sequence; S need not be
   completable).  Print, for each j, the maximal sets with D(S) <= j (as 0/1 strings) and
   the completable ones separately (flag c).  usage: dsets N [jmax] */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int N; static uint32_t Lm[40], Rm[40];
static int valid(uint32_t S,int m){ return __builtin_popcount(S&Lm[m])==__builtin_popcount(S&Rm[m]); }
int main(int argc,char**argv){ N=atoi(argv[1]); int jmax=argc>2?atoi(argv[2]):3;
  for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m; for(int d=1;d<=r;d++){Lm[m]|=1u<<(m-d-1); Rm[m]|=1u<<(m+d-1);} }
  uint32_t F=(1u<<N)-1; unsigned char *b=malloc((size_t)(F+1)*(N+1)); for(size_t i=0;i<(size_t)(F+1)*(N+1);i++) b[i]=255;
  unsigned char *D=malloc(F+1), *comp=calloc(F+1,1); b[0]=1;
  comp[F]=1; for(int64_t S=F;S>=0;S--){ if(comp[S]) continue; for(int m=1;m<=N;m++) if(!(S>>(m-1)&1)&&valid(S,m)&&comp[S|(1u<<(m-1))]){comp[S]=1;break;} }
  for(uint32_t S=0;S<=F;S++){ int d=255;
    for(int l=0;l<=N;l++){ int v=b[(size_t)S*(N+1)+l]; if(v==255) continue; if(v<d) d=v; if(S==F) continue;
      for(int m=1;m<=N;m++){ if(S>>(m-1)&1) continue; if(!valid(S,m)) continue;
        int nv=v+(m<l); size_t j=(size_t)(S|(1u<<(m-1)))*(N+1)+m; if(nv<b[j]) b[j]=nv; } }
    D[S]= S==0?0:d; }
  for(int j=1;j<=jmax;j++){ printf("j=%d maximal sets with D<=j:\n",j);
    for(uint32_t S=1;S<=F;S++){ if(D[S]>j) continue; int maxl=1;
      for(int m=1;m<=N;m++) if(!(S>>(m-1)&1) && D[S|(1u<<(m-1))]<=j){maxl=0;break;}
      if(!maxl) continue; printf("  "); for(int m=1;m<=N;m++) putchar(S>>(m-1)&1?'#':'.'); printf("  |S|=%d%s\n",__builtin_popcount(S),comp[S]?" c":""); } }
  return 0; }

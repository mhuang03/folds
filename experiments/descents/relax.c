/* min number of ascending runs (and whether completable) over sequences in a relaxed class.
   x = L - R (earlier panels in the left / right part of the window of m).
   mode 0 K: |x| <= K.
   mode 1:   left-half m (2m < N+1): x <= 0;  right-half: x >= 0;  centre: x = 0.
   mode 2:   left-half m: x >= 0;  right-half: x <= 0;  centre: x = 0.
   mode 3:   left-half m: x = 0 only (right half unconstrained).
   usage: relax mode K Nmax.  Subset DP: best[S][last] = min runs. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int N, MODE, K; static uint32_t Lm[40], Rm[40];
static int ok(uint32_t S, int m){
  int x=__builtin_popcount(S&Lm[m])-__builtin_popcount(S&Rm[m]);
  int h = 2*m < N+1 ? -1 : (2*m > N+1 ? 1 : 0);
  switch(MODE){
    case 0: return x<=K && x>=-K;
    case 1: return h<0 ? x<=0 : h>0 ? x>=0 : x==0;
    case 2: return h<0 ? x>=0 : h>0 ? x<=0 : x==0;
    case 3: return h<=0 ? x==0 : 1;
  } return 0; }
int main(int argc,char**argv){ MODE=atoi(argv[1]); K=atoi(argv[2]); int NM=atoi(argv[3]);
  for(N=1;N<=NM;N++){
    for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m; Lm[m]=Rm[m]=0; for(int d=1;d<=r;d++){Lm[m]|=1u<<(m-d-1); Rm[m]|=1u<<(m+d-1);} }
    uint32_t F=(1u<<N)-1; unsigned char *b=malloc((size_t)(F+1)*(N+1)); for(size_t i=0;i<(size_t)(F+1)*(N+1);i++) b[i]=255;
    b[0]=1; /* last=0, runs=1 */
    for(uint32_t S=0;S<F;S++) for(int l=0;l<=N;l++){ int v=b[(size_t)S*(N+1)+l]; if(v==255) continue;
      for(int m=1;m<=N;m++){ if(S>>(m-1)&1) continue; if(!ok(S,m)) continue;
        int nv=v+(m<l); size_t j=(size_t)(S|(1u<<(m-1)))*(N+1)+m; if(nv<b[j]) b[j]=nv; } }
    int best=255; for(int l=1;l<=N;l++) if(b[(size_t)F*(N+1)+l]<best) best=b[(size_t)F*(N+1)+l];
    int lg=0; while((2<<lg)<=N+1) lg++;
    printf("mode=%d K=%d N=%d minruns=%d  lg(N+1)=%d%s\n",MODE,K,N,best,lg,best<lg?"  <-- FAILS":""); fflush(stdout); free(b); }
  return 0; }

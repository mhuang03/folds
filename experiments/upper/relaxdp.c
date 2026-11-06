/* relaxdp.c -- exact count (subset DP) of orderings of [1..N] in which every panel of a chosen
   constraint set C is valid (balanced window) when placed; other panels are unconstrained.
   usage: ./relaxdp N mode   (modes as in relax.c: 0 all, 1 left half, 2 block (n1/2,n1], 3 m<=n1/2)
   prints ln(count) and deficit (ln N! - ln count)/N. Memory 2^N doubles. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
int main(int argc,char**argv){ int N=atoi(argv[1]), mode=atoi(argv[2]); int n1=(N+1)/2;
  uint64_t Lm[64],Rm[64]; int con[64];
  for(int m=1;m<=N;m++){ int D=m-1<N-m?m-1:N-m; Lm[m]=Rm[m]=0;
    for(int d=1;d<=D;d++){Lm[m]|=1ULL<<(m-d-1);Rm[m]|=1ULL<<(m+d-1);}
    int c=0; if(mode==0)c=1; else if(mode==1)c=(m<=n1); else if(mode==2)c=(2*m>n1&&m<=n1); else if(mode==3)c=(2*m<=n1); con[m]=c; }
  uint64_t NS=1ULL<<N; double*g=calloc(NS,sizeof(double)); g[0]=1;
  for(uint64_t S=0;S<NS-1;S++){ if(g[S]==0)continue;
    for(int m=1;m<=N;m++){ uint64_t b=1ULL<<(m-1); if(S&b)continue;
      if(con[m] && __builtin_popcountll(S&Lm[m])!=__builtin_popcountll(S&Rm[m])) continue;
      g[S|b]+=g[S]; } }
  double lc=log(g[NS-1]), lf=lgamma(N+1.0);
  printf("N=%d mode=%d count=%.6g lncount=%.4f deficit/N=%.4f\n",N,mode,g[NS-1],lc,(lf-lc)/N); return 0; }

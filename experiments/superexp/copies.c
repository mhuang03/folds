// Count window copies X of [N] by size and the sequences "order of [N]\X, then copy order of X".
// g(S) = number of valid orderings of S from scratch (subset DP).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int N; uint32_t Lm[40],Rm[40];
int main(int argc,char**argv){
  int NMAX=atoi(argv[1]);
  double a[40]; a[0]=1;
  for(N=1;N<=NMAX;N++){
    for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m; Lm[m]=0;Rm[m]=0;
      for(int d=1;d<=r;d++){Lm[m]|=1u<<(m-d-1);Rm[m]|=1u<<(m+d-1);} }
    uint32_t F=((1u<<N)-1);
    double *g=calloc((size_t)1<<N,sizeof(double)); g[0]=1;
    for(uint32_t S=1;S<=F;S++){double s=0; uint32_t T=S; while(T){int b=__builtin_ctz(T);T&=T-1;
        uint32_t P=S&~(1u<<b); int m=b+1; if(__builtin_popcount(P&Lm[m])==__builtin_popcount(P&Rm[m])) s+=g[P];}
      g[S]=s;}
    a[N]=g[F];
    double cnt[40]={0}, tot[40]={0}; int ncop[40]={0};
    for(uint32_t X=1;X<=F;X++){ int ok=1; uint32_t T=X; while(T){int b=__builtin_ctz(T);T&=T-1;
        uint32_t P=X&~(1u<<b); int m=b+1; if(__builtin_popcount(P&Lm[m])!=__builtin_popcount(P&Rm[m])){ok=0;break;}}
      if(ok){int p=__builtin_popcount(X); ncop[p]++; if(g[F&~X]>0) cnt[p]+=1; tot[p]+=g[F&~X]*a[p];
        if(g[X]!=a[p]) printf("!! g(X)!=a(p) X=%x\n",X);} }
    printf("N=%d a=%.0f\n",N,a[N]);
    for(int p=1;p<N;p++) printf("  p=%2d copies=%5d reachcompl=%5.0f  sum g(Y)a(p)=%.0f frac=%.4f\n",p,ncop[p],cnt[p],tot[p],tot[p]/a[N]);
    free(g);
  }
}

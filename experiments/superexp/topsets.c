// List the half-sets X with the largest w(X) = g(X) g(X^c), with g(X), g(X^c) vs a(n).
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int N; uint32_t Lm[40],Rm[40];
typedef struct{double w; uint32_t X;} E;
static int cmpe(const void*a,const void*b){double x=((E*)a)->w,y=((E*)b)->w;return x<y?1:x>y?-1:0;}
double *G[40]; double a[40];
void build(int n){
  for(int m=1;m<=n;m++){int r=m-1<n-m?m-1:n-m; Lm[m]=0;Rm[m]=0;
    for(int d=1;d<=r;d++){Lm[m]|=1u<<(m-d-1);Rm[m]|=1u<<(m+d-1);} }
  uint32_t F=((1u<<n)-1); double *g=calloc((size_t)1<<n,sizeof(double)); g[0]=1;
  for(uint32_t S=1;S<=F;S++){double s=0; uint32_t T=S; while(T){int b=__builtin_ctz(T);T&=T-1;
      uint32_t P=S&~(1u<<b); int m=b+1; if(__builtin_popcount(P&Lm[m])==__builtin_popcount(P&Rm[m])) s+=g[P];}
    g[S]=s;}
  G[n]=g; a[n]=g[F];
}
int main(int argc,char**argv){
  N=atoi(argv[1]); int K=atoi(argv[2]); int n=N/2;
  for(int k=1;k<=n+1;k++) build(k);
  build(N); double *g=G[N]; uint32_t F=(1u<<N)-1;
  E *e=malloc(sizeof(E)*(1u<<N)); int c=0;
  for(uint32_t X=0;X<=F;X++) if(__builtin_popcount(X)==n){double v=g[X]*g[F&~X]; if(v>0){e[c].w=v;e[c].X=X;c++;}}
  qsort(e,c,sizeof(E),cmpe);
  printf("N=%d a(n)=%.0f a(N-n)=%.0f\n",N,a[n],a[N-n]);
  for(int i=0;i<K&&i<c;i++){ uint32_t X=e[i].X; char s[64]; for(int j=0;j<N;j++) s[j]=(X>>j&1)?'X':'.'; s[N]=0;
    printf("%s  g(X)/a(n)=%.3f g(Y)/a(N-n)=%.3f w/ref=%.4f\n",s,g[X]/a[n],g[F&~X]/a[N-n],e[i].w/(a[n]*a[N-n]));}
}

// Distribution of w(X) = g(X) g(X^c) over half-sets X (|X| = floor(N/2)).
// a(N) = sum_X w(X).  How many X carry the mass?  Compare with a(n)^2.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
int N; uint32_t Lm[40],Rm[40];
static int cmpd(const void*a,const void*b){double x=*(double*)a,y=*(double*)b;return x<y?1:x>y?-1:0;}
int main(int argc,char**argv){
  int NMAX=atoi(argv[1]); double a[40]; a[0]=1;
  for(N=1;N<=NMAX;N++){
    for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m; Lm[m]=0;Rm[m]=0;
      for(int d=1;d<=r;d++){Lm[m]|=1u<<(m-d-1);Rm[m]|=1u<<(m+d-1);} }
    uint32_t F=((1u<<N)-1);
    double *g=calloc((size_t)1<<N,sizeof(double)); g[0]=1;
    for(uint32_t S=1;S<=F;S++){double s=0; uint32_t T=S; while(T){int b=__builtin_ctz(T);T&=T-1;
        uint32_t P=S&~(1u<<b); int m=b+1; if(__builtin_popcount(P&Lm[m])==__builtin_popcount(P&Rm[m])) s+=g[P];}
      g[S]=s;}
    a[N]=g[F];
    if(N<8){free(g);continue;}
    int n=N/2; double *w=malloc(sizeof(double)*(1u<<N)); int cnt=0;
    for(uint32_t X=0;X<=F;X++) if(__builtin_popcount(X)==n){double v=g[X]*g[F&~X]; if(v>0) w[cnt++]=v;}
    qsort(w,cnt,sizeof(double),cmpd);
    double ref=a[n]*a[N-n]; double cum=0; int k50=-1,k90=-1; int big=0;
    for(int i=0;i<cnt;i++){cum+=w[i]; if(k50<0&&cum>=0.5*a[N])k50=i+1; if(k90<0&&cum>=0.9*a[N])k90=i+1; if(w[i]>=ref/16)big++;}
    double H=0; for(int i=0;i<cnt;i++){double p=w[i]/a[N]; H-=p*log(p);}
    printf("N=%2d a=%.4g  a(n)a(N-n)=%.4g  #X>0=%d  top w/ref=%.3f  #X carrying 50%%=%d 90%%=%d  #(w>=ref/16)=%d  entropy=%.2f (e^H=%.0f)\n",
      N,a[N],ref,cnt,w[0]/ref,k50,k90,big,H,exp(H));
    free(g);free(w);
  }
}

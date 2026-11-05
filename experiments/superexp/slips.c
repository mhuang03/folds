// Slip sets: N = 2n, X_D = odds with 2k+1 replaced by 2k for k in D (D subset [1,n-1]).
// Print sum_D g(X_D) g(X_D^c) / a(n)^2 and the number of D with w > 0, by |D|.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int N; uint32_t Lm[40],Rm[40];
double *build(int n,double*an){
  for(int m=1;m<=n;m++){int r=m-1<n-m?m-1:n-m; Lm[m]=0;Rm[m]=0;
    for(int d=1;d<=r;d++){Lm[m]|=1u<<(m-d-1);Rm[m]|=1u<<(m+d-1);} }
  uint32_t F=((1u<<n)-1); double *g=calloc((size_t)1<<n,sizeof(double)); g[0]=1;
  for(uint32_t S=1;S<=F;S++){double s=0; uint32_t T=S; while(T){int b=__builtin_ctz(T);T&=T-1;
      uint32_t P=S&~(1u<<b); int m=b+1; if(__builtin_popcount(P&Lm[m])==__builtin_popcount(P&Rm[m])) s+=g[P];}
    g[S]=s;}
  *an=g[F]; return g;
}
int main(int argc,char**argv){
  int NMAX=atoi(argv[1]);
  for(N=6;N<=NMAX;N+=2){ int n=N/2; double an; double*gn=build(n,&an); free(gn);
    double aN; double *g=build(N,&aN); uint32_t F=(1u<<N)-1;
    double tot=0, byk[40]={0}; int nz[40]={0}, all[40]={0};
    for(uint32_t D=0; D<(1u<<(n-1)); D++){
      uint32_t X=0; for(int i=0;i<n;i++) X|=1u<<(2*i); // odds: panel 2i+1 -> bit 2i
      for(int k=1;k<n;k++) if(D>>(k-1)&1){ X&=~(1u<<(2*k)); X|=1u<<(2*k-1);} // 2k+1 -> 2k
      double w=g[X]*g[F&~X]; int c=__builtin_popcount(D); tot+=w; byk[c]+=w; all[c]++; if(w>0)nz[c]++;
    }
    printf("N=%d a(N)=%.0f a(n)^2=%.0f  sum_D w/a(n)^2=%.3f  ratio a(N)/a(n)^2=%.1f\n",N,aN,an*an,tot/(an*an),aN/(an*an));
    for(int c=0;c<n;c++) printf("   |D|=%d: %d/%d nonzero, sum w/a(n)^2=%.4f\n",c,nz[c],all[c],byk[c]/(an*an));
    free(g);
  }
}

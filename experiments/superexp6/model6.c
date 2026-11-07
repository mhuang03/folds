// C version of superexp5/model5.py (log2 counts) plus the generalised composition
// A(N) >= sum_{s=1}^{d} A(|class s mod d|) for 3 <= d <= DM (any N).
// usage: ./model6.bin MAXN U g DM
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
static long MX; static double U,G; static int DM;
static double *A,*Bv; static double *Mm; static char *Md;
static double mx(double a,double b){return a>b?a:b;}
static double Mf(long x,long y,long r){
  double base=A[x]+A[y]; if(r<=0) return base;
  long key=x*4+(y-x)*2+(r-(x-1)/2); // r in {(x-1)/2, (x-1)/2+1}
  if(r-(x-1)/2<0||r-(x-1)/2>1){ fprintf(stderr,"bad r %ld %ld\n",x,r); exit(1);}
  if(Md[key]) return Mm[key];
  double v=mx(base,(r+1)/2+A[(x+1)/2]+A[y/2]+Mf(x/2,(y+1)/2,r/2));
  Md[key]=1; Mm[key]=v; return v;
}
int main(int argc,char**argv){ MX=atol(argv[1]); U=atof(argv[2]); G=atof(argv[3]); DM=atoi(argv[4]);
  A=calloc(MX+2,sizeof(double)); Bv=calloc(MX+2,sizeof(double)); Mm=calloc(4*(MX+2),sizeof(double)); Md=calloc(4*(MX+2),1);
  for(long N=2;N<=MX;N++){
    double a;
    if(N%2){ long n=N/2; a=1+A[n]+A[n+1];
      if(n>=2){ long e,c; if(n%2==0){e=n;c=n+1;}else{e=n+1;c=n;} a=mx(a,G*n+A[e]+A[c/2]+A[c-c/2]); } }
    else a=mx(Bv[N/2],1+2*A[N/2]);
    for(int d=3;d<=DM&&d<=N;d++){ long m=N/d,r=N%d; a=mx(a,r*A[m+1]+(d-r)*A[m]); }
    A[N]=a;
    // B(N)
    double b=2*A[N];
    if(N%2==0){ long m=N/2; b=mx(b,m+2*A[m]+Bv[m]); }
    else if(N>1) b=mx(b,Mf(N,N,(N-1)/2)+U*N);
    Bv[N]=b;
  }
  for(long lo=16; lo*2<=MX+1; lo*=2){ double mn=1e9; long arg=0; for(long N=lo;N<2*lo;N++){ double v=A[N]/(N*log2((double)N)); if(v<mn){mn=v;arg=N;} }
    printf("[%ld,%ld): min A/(N log2 N) = %.4f at N=%ld\n",lo,2*lo,mn,arg); }
}

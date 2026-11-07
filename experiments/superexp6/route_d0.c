// Numerical model: F(N) = best lower bound for ln a(N) from
//   base: F(2^L) = (2^L/6) ln(2^L/2)  (Lean, SuperExp2: a(N) >= (N/2)^{N/6}, N = 2^L),
//         F(N) >= (N-1) ln 2,
//   generalised composition: F(N) >= sum over residue classes mod d of F(|class|)
//         (sizes floor(N/d), ceil(N/d)), any 2 <= d <= DMAX.
// Prints min over N in dyadic ranges of F(N)/(N ln N).
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
int main(int argc,char**argv){ long M=atol(argv[1]); int DMAX=atoi(argv[2]); int usebase=1; int D0=atoi(argv[3]);
  double *F=malloc(sizeof(double)*(M+1)); F[0]=0; F[1]=0;
  for(long N=2;N<=M;N++){ double b=(N-1)*log(2.0);
    if(usebase && (N&(N-1))==0) { double v=(N/6.0)*log(N/2.0); if(v>b) b=v; }
    for(int d=2; d<=DMAX && d<=N; d++){ long m=N/d, r=N%d; { int o=d; while(o%2==0) o/=2; if(o>D0) continue; } double v=r*F[m+1]+(d-r)*F[m]; if(v>b) b=v; }
    F[N]=b; }
  for(long lo=16; lo*2<=M+1; lo*=2){ double mn=1e9; long arg=0; for(long N=lo;N<2*lo;N++){ double v=F[N]/(N*log(N)); if(v<mn){mn=v;arg=N;} }
    printf("[%ld,%ld): min F/(N lnN) = %.4f at N=%ld   (F(2^L)/(N lnN) = %.4f)\n",lo,2*lo,mn,arg,F[lo]/(lo*log(lo))); }
}

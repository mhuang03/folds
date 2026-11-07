// Controlled greedy descents for the semi-symmetric fold process.
// J(m) = #S in right arm of m - #S in left arm of m; m free is valid iff J(m) = 0.
// Dipole rule: adding x gives +1 on m in [x/2+1, x-1] (x in right arm of m),
//                            -1 on m in [x+1, (N+x)/2] (x in left arm of m).
// Strategy s:
//   0  uniform valid move
//   1  among valid moves, those minimising dPhi (Phi = sum over free m of J(m)^2), with
//      tolerance tol (allowed set = dPhi <= min + tol); uniform in the allowed set
//   2  allowed set = valid moves with dPhi <= 0 (if none: the minimisers)
//   3  allowed set = valid moves with dPhi <= tol * (number of free panels)/N  (relative)
// Output per run: completed?, steps, sum ln|allowed|, sum ln V, mean sigma_J.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
static unsigned long long rs=88172645463325252ULL;
static unsigned long long rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
int main(int argc,char**argv){
  int N=atoi(argv[1]); int strat=atoi(argv[2]); double tol=atof(argv[3]); int runs=atoi(argv[4]);
  if(argc>5) rs=strtoull(argv[5],0,10)*2654435761ULL+1;
  int *J=calloc(N+2,sizeof(int)); char *in=calloc(N+2,1);
  long long *PJ=calloc(N+3,sizeof(long long)); long long *PC=calloc(N+3,sizeof(long long));
  double *dphi=calloc(N+2,sizeof(double)); int *cand=calloc(N+2,sizeof(int));
  long *P0=calloc(N+3,sizeof(long)),*Pm=calloc(N+3,sizeof(long)),*Pp=calloc(N+3,sizeof(long));
  int done=0; double totA=0,totV=0;
  for(int run=0;run<runs;run++){
    memset(J,0,(N+2)*sizeof(int)); memset(in,0,N+2);
    double sA=0,sV=0,ssig=0; int k;
    for(k=0;k<N;k++){
      // prefix sums over free panels of J and of 1
      PJ[0]=0;PC[0]=0;
      for(int m=1;m<=N;m++){ PJ[m]=PJ[m-1]+(in[m]?0:J[m]); PC[m]=PC[m-1]+(in[m]?0:1); }
      int V=0; double mn=1e18; double s2=0,s1=0; int f=0;
      for(int m=1;m<=N;m++) if(!in[m]){ f++; s1+=J[m]; s2+=(double)J[m]*J[m]; }
      ssig += sqrt(fmax(0,s2/f-(s1/f)*(s1/f)));
      // we need sum of J^2 change: plus region A=[x/2+1,x-1]: sum(2J+1); minus region B=[x+1,(N+x)/2]: sum(-2J+1)
      // need prefix of J over free (have) ; prefix of count (have)
      if(strat>=4){ // prefix counts of free panels with J==0, J==-1, J==+1
        P0[0]=Pm[0]=Pp[0]=0;
        for(int m=1;m<=N;m++){ int fr=!in[m]; P0[m]=P0[m-1]+(fr&&J[m]==0); Pm[m]=Pm[m-1]+(fr&&J[m]==-1); Pp[m]=Pp[m-1]+(fr&&J[m]==1); }
      }
      for(int x=1;x<=N;x++) if(!in[x] && J[x]==0){
        int a1=x/2+1,a2=x-1,b1=x+1,b2=(N+x)/2;
        double d=0;
        if(strat<4){
        if(a2>=a1) d += 2.0*(PJ[a2]-PJ[a1-1]) + (PC[a2]-PC[a1-1]);
        if(b2>=b1) d += -2.0*(PJ[b2]-PJ[b1-1]) + (PC[b2]-PC[b1-1]);
        } else { // d = -(number of valid moves after x)
          long v=P0[N]-1;
          if(a2>=a1) v += -(P0[a2]-P0[a1-1]) + (Pm[a2]-Pm[a1-1]);
          if(b2>=b1) v += -(P0[b2]-P0[b1-1]) + (Pp[b2]-Pp[b1-1]);
          d=-(double)v; if(k==N-1) d=0;
          if(v<=0 && k<N-1) d=1e9; // dead next
        }
        dphi[V]=d; cand[V]=x; V++; if(d<mn) mn=d;
      }
      if(V==0) break;
      int A=0; int *al=cand; // compact allowed into front
      int nA=0;
      for(int i=0;i<V;i++){
        int ok;
        if(strat==0) ok=1;
        else if(strat==1) ok = dphi[i] <= mn+tol;
        else if(strat==2) ok = dphi[i] <= 0;
        else if(strat==3) ok = dphi[i] <= mn + tol*(N-k);
        else if(strat==4) ok = dphi[i] <= mn + tol;            // near-max mobility
        else ok = dphi[i] <= mn*(1-tol) && dphi[i] < 1e8;      // mobility >= (1-tol) max
        if(ok){ cand[nA]=cand[i]; dphi[nA]=dphi[i]; nA++; }
      }
      if(nA==0){ for(int i=0;i<V;i++) if(dphi[i]<=mn){ cand[nA]=cand[i]; nA++; } }
      A=nA; (void)al;
      sA+=log(A); sV+=log(V);
      int x=cand[rnd()%A];
      in[x]=1;
      for(int m=x/2+1;m<=x-1;m++) J[m]++;
      for(int m=x+1;m<=(N+x)/2;m++) J[m]--;
    }
    if(k==N) done++;
    totA+=sA; totV+=sV;
    printf("run %d: steps %d/%d  sumlnA %.1f  sumlnV %.1f  lnN! %.1f  meansig %.2f\n",run,k,N,sA,sV,lgamma(N+1.0),ssig/(k+1));
    fflush(stdout);
  }
  printf("N=%d strat=%d tol=%g completed %d/%d  mean sumlnA/(N lnN) %.3f\n",N,strat,tol,done,runs,totA/runs/(N*log(N)));
  return 0;
}

/* relax.c -- SMC estimate of the number of permutations of [1..N] satisfying only the
   constraints C_m for m in a chosen set (windows of the N-strip).
   usage: ./relax N mode P seed
     mode 0: all m (a(N));  mode 1: left half m <= (N+1)/2 (L(N));
     mode 2: block m in (n1/2, n1], n1 = (N+1)/2;  mode 3: m <= n1/2 (lower left quarter)
   prints ln(count) estimate and deficit (ln N! - ln count)/N.
   J(m) = #(S in right arm) - #(S in left arm), updated by the dipole lemma. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
static uint64_t rs=88172645463325252ULL;
static double rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return (rs>>11)*(1.0/9007199254740992.0);}
int main(int argc,char**argv){ int N=atoi(argv[1]), mode=atoi(argv[2]), P=atoi(argv[3]); rs+=atoi(argv[4])*1000003ULL;
  int n1=(N+1)/2; char *con=calloc(N+2,1);
  for(int m=1;m<=N;m++){ int c=0; if(mode==0)c=1; else if(mode==1)c=(m<=n1); else if(mode==2)c=(2*m>n1 && m<=n1); else if(mode==3) c=(2*m<=n1); con[m]=c; }
  int *J=calloc((size_t)P*(N+2),sizeof(int)), *J2=calloc((size_t)P*(N+2),sizeof(int));
  char *in=calloc((size_t)P*(N+2),1), *in2=calloc((size_t)P*(N+2),1);
  int *V=malloc(sizeof(int)*P); double *cw=malloc(sizeof(double)*P);
  double lc=0;
  for(int k=0;k<N;k++){
    double tot=0; for(int p=0;p<P;p++){ int*j=J+(size_t)p*(N+2); char*s=in+(size_t)p*(N+2); int v=0;
      for(int m=1;m<=N;m++) if(!s[m] && (!con[m] || j[m]==0)) v++; V[p]=v; tot+=v; cw[p]=tot; }
    if(tot==0){ printf("extinct at k=%d\n",k); return 0; }
    lc+=log(tot/P);
    for(int p=0;p<P;p++){ double u=rnd()*tot; int lo=0,hi=P-1; while(lo<hi){int mid=(lo+hi)/2; if(cw[mid]>u)hi=mid; else lo=mid+1;}
      int*j=J+(size_t)lo*(N+2); char*s=in+(size_t)lo*(N+2);
      int t=(int)(rnd()*V[lo]), x=0; for(int m=1;m<=N;m++) if(!s[m] && (!con[m]||j[m]==0)){ if(t==0){x=m;break;} t--; }
      int*jj=J2+(size_t)p*(N+2); char*ss=in2+(size_t)p*(N+2); memcpy(jj,j,sizeof(int)*(N+2)); memcpy(ss,s,N+2); ss[x]=1;
      for(int q=x/2+1;q<x;q++) jj[q]++;
      for(int q=x+1;q<=(N+x)/2;q++) jj[q]--; }
    int*tj=J;J=J2;J2=tj; char*ts=in;in=in2;in2=ts; }
  double lf=lgamma(N+1.0);
  printf("N=%d mode=%d P=%d lncount=%.3f deficit/N=%.4f\n",N,mode,P,lc,(lf-lc)/N);
  return 0; }

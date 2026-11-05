/* Explicit enumeration of semi-symmetric fold sequences with statistic histograms.
   usage: stats N
   For each statistic prints "name: c_0 c_1 ... " (coefficient list of its generating poly).
   statistics:
     pos1   step (1..N) at which panel 1 is placed   (index 0 unused)
     posN   step at which panel N is placed
     first  value of a_1
     free   #steps whose window contains no earlier panel (includes r=0 steps)
     full   #steps whose window is completely filled (includes r=0 steps)
     zero   #steps with r = 0 or window empty or full  ("trivially balanced")
     des    #descents a_k > a_{k+1}
     cross  #k with a_k, a_{k+1} on strictly opposite sides of (N+1)/2
     inv    #inversions
     mid    (odd N) step at which the middle panel is placed
     lrmax  #left-to-right maxima
*/
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define MX 40
static int N; static uint64_t L[MX],R[MX],W[MX];
static int seq[MX];
static uint64_t H_pos1[MX],H_posN[MX],H_first[MX],H_free[MX],H_full[MX],H_zero[MX],H_des[MX],H_cross[MX],H_mid[MX],H_lr[MX];
static uint64_t H_inv[MX*MX];
static int sfree[MX], sfull[MX];
static uint64_t total=0;
static void rec(int k, uint64_t S, int nfree, int nfull, int nzero){
  if(k==N){
    total++;
    int p1=0,pN=0,pm=0,des=0,cr=0,inv=0,lr=0,mx=0;
    for(int i=0;i<N;i++){int m=seq[i];
      if(m==1)p1=i+1; if(m==N)pN=i+1; if(2*m==N+1)pm=i+1;
      if(m>mx){mx=m;lr++;}
      if(i+1<N){int q=seq[i+1]; if(m>q)des++; if((2*m-(N+1))*(2*q-(N+1))<0)cr++;}
      for(int j=i+1;j<N;j++) if(seq[j]<m) inv++;
    }
    H_pos1[p1]++;H_posN[pN]++;H_first[seq[0]]++;H_free[nfree]++;H_full[nfull]++;H_zero[nzero]++;
    H_des[des]++;H_cross[cr]++;H_inv[inv]++;H_lr[lr]++; if(N%2)H_mid[pm]++;
    return;
  }
  for(int m=1;m<=N;m++){ uint64_t b=1ULL<<(m-1); if(S&b)continue;
    int a=__builtin_popcountll(S&L[m]), r=__builtin_popcountll(S&R[m]);
    if(a!=r) continue;
    int w=__builtin_popcountll(W[m]);
    int e=(a==0), f=(2*a==w);
    seq[k]=m; rec(k+1,S|b,nfree+e,nfull+f,nzero+(e||f));
  }
}
static void pr(const char*nm,uint64_t*h,int len){printf("%s:",nm);for(int i=0;i<len;i++)printf(" %llu",(unsigned long long)h[i]);printf("\n");}
int main(int argc,char**argv){
  N=atoi(argv[1]);
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m;L[m]=R[m]=0;
    for(int d=1;d<=D;d++){L[m]|=1ULL<<(m-d-1);R[m]|=1ULL<<(m+d-1);} W[m]=L[m]|R[m];}
  rec(0,0,0,0,0);
  printf("N %d total %llu\n",N,(unsigned long long)total);
  pr("pos1",H_pos1,N+1); pr("posN",H_posN,N+1); pr("first",H_first,N+1);
  pr("free",H_free,N+1); pr("full",H_full,N+1); pr("zero",H_zero,N+1);
  pr("des",H_des,N); pr("cross",H_cross,N); pr("lrmax",H_lr,N+1);
  pr("inv",H_inv,N*(N-1)/2+1);
  if(N%2) pr("mid",H_mid,N+1);
  return 0;
}

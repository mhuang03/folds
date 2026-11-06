/* steps.c N maxd x1 x2 ...: minimal step sequences (valid steps after the background) making
   the set inward (Theorem G); prints the final step sets at minimal depth (one order each). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 W;
static int N; static W L[130], R[130];
static int pc(W x){return __builtin_popcountll((unsigned long long)x)+__builtin_popcountll((unsigned long long)(x>>64));}
static int reachv(int m){int a=m-1,b=N-m;return a<b?a:b;}
static int imb(W S,int m){return pc(S&L[m])-pc(S&R[m]);}
static int centre(W B){ int maxneg=0,minpos=N+1;
  for(int m=1;m<=N;m++){ if((B>>(m-1))&1)continue; int I=imb(B,m); if(I<0&&m>maxneg)maxneg=m; if(I>0&&m<minpos)minpos=m;}
  return maxneg<minpos ? maxneg : -1; }
static int stk[20]; static int found=0, maxprint=40;
static W seenS[200000]; static int nseen=0;
static void go(W S,int k,int d){
  if(k==0){ int c=centre(S); if(c>=0){ for(int i=0;i<nseen;i++)if(seenS[i]==S)return; if(nseen<200000)seenS[nseen++]=S;
      found++; if(found<=maxprint){printf("  steps:");for(int i=0;i<d;i++)printf(" %d",stk[i]);printf("  (negmax %d)\n",c);} } return;}
  for(int m=1;m<=N;m++){ if((S>>(m-1))&1)continue; if(imb(S,m)==0){stk[d]=m; go(S|((W)1<<(m-1)),k-1,d+1);} } }
int main(int argc,char**argv){
  N=atoi(argv[1]); int maxd=atoi(argv[2]); if(getenv("MAXP"))maxprint=atoi(getenv("MAXP"));
  for(int m=1;m<=N;m++){int r=reachv(m);L[m]=R[m]=0;for(int d=1;d<=r;d++){L[m]|=(W)1<<(m-d-1);R[m]|=(W)1<<(m+d-1);}}
  W B=0; for(int i=3;i<argc;i++)B|=(W)1<<(atoi(argv[i])-1);
  for(int k=0;k<=maxd;k++){ found=0; nseen=0; go(B,k,0); if(found){printf("depth %d: %d sets\n",k,found);return 0;} }
  printf("none up to %d\n",maxd); return 0; }

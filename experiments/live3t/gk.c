/* gk.c N K x1 x2 ...: valid steps (at most K) after the set {x1, x2, ...} of [N], then
   Theorem G (any centre); prints the first step list found and the centre c2, or NONE.
   Steps are tried in the order of the env ORDER (comma list), else 1..N. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned _BitInt(256) W;
static int N; static W Lm[260], Rm[260];
static int pc(W x){int s=0;for(int i=0;i<4;i++){s+=__builtin_popcountll((unsigned long long)x);x>>=64;}return s;}
static int imb(W S,int m){return pc(S&Lm[m])-pc(S&Rm[m]);}
static int centre(W B){ int maxneg=0,minpos=N+1;
  for(int m=1;m<=N;m++){ if((B>>(m-1))&1)continue; int I=imb(B,m); if(I<0&&m>maxneg)maxneg=m; if(I>0&&m<minpos)minpos=m;}
  return maxneg<minpos ? 2*maxneg+1 : -1; }
static int stk[64], ord[260]; static long nodes;
static int gk(W S,int k,int d){ int c=centre(S); if(c>=0){stk[d]=c;return d+1;} if(!k)return 0; nodes++;
  for(int i=0;i<N;i++){ int m=ord[i]; if((S>>(m-1))&1)continue; if(imb(S,m)==0){ stk[d]=m; int r=gk(S|((W)1<<(m-1)),k-1,d+1); if(r)return r;}} return 0;}
int main(int argc,char**argv){
  N=atoi(argv[1]); int K=atoi(argv[2]); W S=0;
  for(int i=3;i<argc;i++){int x=atoi(argv[i]); S|=(W)1<<(x-1);}
  for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m;Lm[m]=Rm[m]=0;for(int d=1;d<=r;d++){Lm[m]|=(W)1<<(m-d-1);Rm[m]|=(W)1<<(m+d-1);}}
  for(int i=0;i<N;i++)ord[i]=i+1;
  for(int k=0;k<=K;k++){ int d=gk(S,k,0); if(d){ printf("steps:"); for(int i=0;i<d-1;i++)printf(" %d",stk[i]); printf(" c2=%d\n",stk[d-1]); return 0;} }
  printf("NONE\n"); return 0; }

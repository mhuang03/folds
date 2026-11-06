/* depth.c maxd < lines "N a b c": minimal number of valid steps after {a,b,c} making the set
   inward (Theorem G), or -1 if more than maxd; prints "N a b c depth steps". */
#include <stdio.h>
#include <stdlib.h>
typedef unsigned __int128 W;
static int N; static W L[130], R[130];
static int pc(W x){return __builtin_popcountll((unsigned long long)x)+__builtin_popcountll((unsigned long long)(x>>64));}
static int reachv(int m){int a=m-1,b=N-m;return a<b?a:b;}
static int imb(W S,int m){return pc(S&L[m])-pc(S&R[m]);}
static int inw(W B){ int maxneg=0,minpos=N+1;
  for(int m=1;m<=N;m++){ if((B>>(m-1))&1)continue; int I=imb(B,m); if(I<0&&m>maxneg)maxneg=m; if(I>0&&m<minpos)minpos=m;}
  return maxneg<minpos; }
static int stk[20];
static int go(W S,int k,int d){ if(k==0)return inw(S);
  for(int m=1;m<=N;m++){ if((S>>(m-1))&1)continue; if(imb(S,m)==0){stk[d]=m; if(go(S|((W)1<<(m-1)),k-1,d+1))return 1;} } return 0;}
int main(int argc,char**argv){
  int maxd=atoi(argv[1]); int n,a,b,c;
  while(scanf("%d %d %d %d",&n,&a,&b,&c)==4){
    N=n; for(int m=1;m<=N;m++){int r=reachv(m);L[m]=R[m]=0;for(int d=1;d<=r;d++){L[m]|=(W)1<<(m-d-1);R[m]|=(W)1<<(m+d-1);}}
    W B=((W)1<<(a-1))|((W)1<<(b-1))|((W)1<<(c-1)); int res=-1;
    for(int k=0;k<=maxd;k++) if(go(B,k,0)){res=k;break;}
    printf("%d %d %d %d %d",N,a,b,c,res); if(res>0)for(int i=0;i<res;i++)printf(" %d",stk[i]); printf("\n"); fflush(stdout);
  }
  return 0;}

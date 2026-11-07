// Theorem G coverage of 3-subsets of [2,N-1], with up to K valid steps.
// usage: gk N K [v]   (v: print the residual)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int N;
static int reachf(int m){int a=m-1,b=N-m;return a<b?a:b;}
static int imb(const char*B,int m){int r=reachf(m),s=0;for(int x=m-r;x<m;x++)s+=B[x];for(int x=m+1;x<=m+r;x++)s-=B[x];return s;}
static int G(const char*B){ // separation criterion of Theorem G
  int maxneg=0,minpos=N+1;
  for(int m=1;m<=N;m++){if(B[m])continue;int i=imb(B,m);if(i<0)maxneg=m;else if(i>0&&m<minpos)minpos=m;}
  return maxneg<minpos;}
static int GK(char*B,int k,int*steps){
  if(G(B))return 1; if(k==0)return 0;
  for(int m=1;m<=N;m++){if(B[m])continue;if(imb(B,m))continue;B[m]=1;steps[0]=m;int ok=GK(B,k-1,steps+1);B[m]=0;if(ok)return 1;}
  return 0;}
int main(int argc,char**argv){N=atoi(argv[1]);int K=atoi(argv[2]);int verbose=argc>3;
  char B[400];long cnt[12]={0},tot=0;
  for(int a=2;a<=N-1;a++)for(int b=a+1;b<=N-1;b++)for(int c=b+1;c<=N-1;c++){
    if(a+c>N+1)continue; // canonical up to mirror
    tot++;memset(B,0,sizeof B);B[a]=B[b]=B[c]=1;int st[12];int k;
    for(k=0;k<=K;k++){if(GK(B,k,st))break;}
    cnt[k]++;
    if(k>K && verbose)printf("R %d %d %d %d\n",N,a,b,c);
  }
  printf("N=%d tot=%ld",N,tot);for(int k=0;k<=K+1;k++)printf(" k%d=%ld",k,cnt[k]);printf("\n");}

/* gdepth.c N: for each interior 3-set, the least t such that for some centre c2 the first t
   steps of the nearest-to-centre greedy (centre c2) are valid and leave a background that
   satisfies Theorem G (any centre).  Histogram of t; sets with t > T printed (mode v T). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int N;
static int Gsep(const char*B){ static int P[600]; P[0]=0; for(int x=1;x<=N;x++)P[x]=P[x-1]+B[x];
  int maxneg=0,minpos=N+1;
  for(int m=1;m<=N;m++){ if(B[m])continue; int r=m-1<N-m?m-1:N-m; int I=(P[m-1]-P[m-1-r])-(P[m+r]-P[m]);
    if(I<0)maxneg=m; else if(I>0&&m<minpos)minpos=m; }
  return maxneg<minpos;}
static int depth(const char*B0,int c2,int tmax){ char B[400]; memcpy(B,B0,N+2); int P[400];
  for(int t=0;t<=tmax;t++){ if(Gsep(B))return t;
    P[0]=0; for(int x=1;x<=N;x++)P[x]=P[x-1]+B[x];
    int best=-1,bd=1<<30;
    for(int m=1;m<=N;m++){ if(B[m])continue; int r=m-1<N-m?m-1:N-m; int I=(P[m-1]-P[m-1-r])-(P[m+r]-P[m]);
      if(I)continue; int d=abs(2*m-c2); if(d<bd){bd=d;best=m;} }
    if(best<0)return 1000; B[best]=1; }
  return 1000;}
int main(int argc,char**argv){ N=atoi(argv[1]); int T=argc>2?atoi(argv[2]):1000; long h[1001]={0}; char B[400];
  for(int a=2;a<=N-1;a++)for(int b=a+1;b<=N-1;b++)for(int c=b+1;c<=N-1;c++){ if(a+c>N+1)continue;
    memset(B,0,N+2);B[a]=B[b]=B[c]=1; int best=1000,bc=0;
    for(int c2=2;c2<=2*N;c2++){int d=depth(B,c2,best<N?best:N); if(d<best){best=d;bc=c2;}}
    h[best]++; if(best>T)printf("D %d %d %d %d t=%d c2=%d\n",N,a,b,c,best,bc); }
  printf("N=%d",N); for(int t=0;t<=1000;t++)if(h[t])printf(" t%d:%ld",t,h[t]); printf("\n");}

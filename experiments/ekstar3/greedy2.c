/* greedy2.c N [mode]: for each interior 3-set (canonical), the set of centres c2 for which the
   nearest-to-centre greedy completes.  Summary: how often the middle c2 = N+1 works, and the
   sets where it fails, with the successful centres (mode v). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int N;
static int run(const char*B0,int c2){ char B[400]; memcpy(B,B0,N+2); int P[400];
  int free_=0; for(int m=1;m<=N;m++)if(!B[m])free_++;
  while(free_){ P[0]=0; for(int x=1;x<=N;x++)P[x]=P[x-1]+B[x];
    int best=-1,bd=1<<30;
    for(int m=1;m<=N;m++){ if(B[m])continue; int r=m-1<N-m?m-1:N-m; int I=(P[m-1]-P[m-1-r])-(P[m+r]-P[m]);
      if(I)continue; int d=abs(2*m-c2); if(d<bd){bd=d;best=m;} }
    if(best<0)return 0; B[best]=1; free_--; }
  return 1;}
int main(int argc,char**argv){ N=atoi(argv[1]); int v=argc>2; long tot=0,mid=0; char B[400];
  for(int a=2;a<=N-1;a++)for(int b=a+1;b<=N-1;b++)for(int c=b+1;c<=N-1;c++){ if(a+c>N+1)continue; tot++;
    memset(B,0,N+2);B[a]=B[b]=B[c]=1;
    if(run(B,N+1)){mid++;continue;}
    if(v){printf("F %d %d %d %d :",N,a,b,c); for(int c2=2;c2<=2*N;c2++)if(run(B,c2))printf(" %d",c2); printf("\n");}
  }
  printf("N=%d tot=%ld middle=%ld fail=%ld\n",N,tot,mid,tot-mid);}

/* greedy.c N: for every interior 3-set D (canonical), does the deterministic greedy
   "place the valid free panel nearest to the centre c2/2 (ties: left)" complete [N] for
   some centre c2 in [2, 2N]?  Prints the sets for which no centre works. */
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
int main(int argc,char**argv){ N=atoi(argv[1]); long tot=0,bad=0; char B[400];
  for(int a=2;a<=N-1;a++)for(int b=a+1;b<=N-1;b++)for(int c=b+1;c<=N-1;c++){ if(a+c>N+1)continue; tot++;
    memset(B,0,N+2);B[a]=B[b]=B[c]=1; int ok=0;
    for(int c2=2;c2<=2*N&&!ok;c2++)ok=run(B,c2);
    if(!ok){bad++; if(argc>2)printf("B %d %d %d %d\n",N,a,b,c);} }
  printf("N=%d tot=%ld nogreedy=%ld\n",N,tot,bad);}

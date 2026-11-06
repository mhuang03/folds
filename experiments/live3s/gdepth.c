/* gdepth.c N0 N1 D [all]: for {1, 2, c} (valid, not dead) not settled by the closed-form near
   copies O, F1, F2 (fams.py), the least number d <= D of valid steps after which the background
   satisfies Theorem G (some centre); prints the steps.  With "all", every c is tried. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 W;
static int N; static W Lm[260], Rm[260];
static int pc(W x){return __builtin_popcountll((unsigned long long)x)+__builtin_popcountll((unsigned long long)(x>>64));}
static int imb(W S,int m){return pc(S&Lm[m])-pc(S&Rm[m]);}
static int centreOK(W B){ int maxneg=0,minpos=N+1;
  for(int m=1;m<=N;m++){ if((B>>(m-1))&1)continue; int I=imb(B,m); if(I<0&&m>maxneg)maxneg=m; if(I>0&&m<minpos)minpos=m;}
  return maxneg<minpos; }
static int path[16];
static int dfs(W S,int d){
  if(centreOK(S))return 1;
  if(d==0)return 0;
  for(int m=1;m<=N;m++){ if((S>>(m-1))&1)continue; if(imb(S,m)==0){ path[d-1]=m; if(dfs(S|((W)1<<(m-1)),d-1))return 1;}}
  return 0;}
static int deadp(int p,int g){ return (p%2==1 && p>=7 && (g==p-1||g==p)); }
static int fam(int c){
  if(N%4==1 && c%2==1 && c>=7 && c<=N-4) return 1;
  if(N%2==0 && c%2==1 && c>=5 && !deadp(N/2,(c+1)/2)) return 1;
  if(N%4==3 && c%2==0 && c>=6 && c<=N-5) return 1;
  return 0; }
int main(int argc,char**argv){
  int N0=atoi(argv[1]),N1=atoi(argv[2]),D=atoi(argv[3]); int all=argc>4;
  for(N=N0;N<=N1;N++){
    if(N>127){fprintf(stderr,"N <= 127\n");return 1;}
    for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m;Lm[m]=Rm[m]=0;for(int d=1;d<=r;d++){Lm[m]|=(W)1<<(m-d-1);Rm[m]|=(W)1<<(m+d-1);}}
    int cmax = (N%2==1)? N-2 : N;
    printf("N=%d (mod 8 = %d):",N,N%8);
    for(int c=3;c<=cmax;c++){ if(!all && fam(c))continue;
      W B=((W)1)|((W)1<<1)|((W)1<<(c-1)); int ok=-1;
      for(int d=0;d<=D;d++){ if(dfs(B,d)){ok=d;break;} }
      if(ok<0) printf(" %d:X",c); else { printf(" %d:%d",c,ok); }
    }
    printf("\n"); fflush(stdout);
  }
  return 0;}

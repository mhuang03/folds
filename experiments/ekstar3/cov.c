/* cov.c N [K] [flags]: coverage of the interior 3-subsets {a<b<c} of [2, N-1] (canonical:
   a + c <= N + 1) by
     G : Theorem G (separation form) for the triple itself,
     T : a transfer through a window copy of Live3q (Z, right-aligned Beatty, residue class,
         multiples, swapped Beatty, chiY) of the triple or its mirror image, from a preimage
         triple of [p], p < N, that is KNOWN: interior in [p] (induction hypothesis E*_3),
         or p <= 50, p != 7, valid and not dead (Live3q.good3_le_50), or Theorem G in [p];
     S : Theorem G after <= K valid steps.
   Prints the residual ("R N a b c") and a summary line.
   env ONLYINT=1: KNOWN = interior only (no Good3, no G for the preimage). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int N;
static int reachN(int n,int m){int a=m-1,b=n-m;return a<b?a:b;}
/* imbalance via prefix sums */
static int Gsep(int n,const char*B){ static int P[600]; P[0]=0; for(int x=1;x<=n;x++)P[x]=P[x-1]+B[x];
  int maxneg=0,minpos=n+1;
  for(int m=1;m<=n;m++){ if(B[m])continue; int r=reachN(n,m); int I=(P[m-1]-P[m-1-r])-(P[m+r]-P[m]);
    if(I<0)maxneg=m; else if(I>0&&m<minpos)minpos=m; }
  return maxneg<minpos;}
static int imbB(int n,const char*B,int m){int r=reachN(n,m),s=0;for(int x=m-r;x<m;x++)s+=B[x];for(int x=m+1;x<=m+r;x++)s-=B[x];return s;}
static int GK(int n,char*B,int k){ if(Gsep(n,B))return 1; if(!k)return 0;
  for(int m=1;m<=n;m++){ if(B[m]||imbB(n,B,m))continue; B[m]=1; int ok=GK(n,B,k-1); B[m]=0; if(ok)return 1;} return 0;}
static int imbn(int n,int *xs,int k,int m){int r=reachN(n,m),s=0;for(int i=0;i<k;i++){int x=xs[i];if(m-r<=x&&x<m)s++;if(m<x&&x<=m+r)s--;}return s;}
static int valid3n(int n,int a,int b,int c){int t[3]={a,b,c};int P[6][3]={{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
  for(int q=0;q<6;q++){int x=t[P[q][0]],y=t[P[q][1]],z=t[P[q][2]];int s1[1]={x},s2[2]={x,y};
    if(imbn(n,s1,1,y)==0&&imbn(n,s2,2,z)==0)return 1;}return 0;}
static int isdeadN(int n,int a,int b,int c){
  if(a==1&&b%2==0&&c==b+1&&4<=b&&2*b<=n+3)return 1;
  if(c==n&&b==a+1&&(n-a)%2==0&&4<=n-a&&2*(n-a)<=n+3&&a<n)return 1;
  if(n%2==1&&n>=7&&((a==1&&b==2&&(c==n-1||c==n))||(b==n-1&&c==n&&(a==1||a==2))))return 1;
  if(n==7&&a==1&&b==4&&c==7)return 1;
  return 0;}
static int onlyint;
static int known(int p,int i,int j,int l){
  if(i>=2&&l<=p-1)return 1;
  if(onlyint)return 0;
  if((p<=50||getenv("GOOD3ALL"))&&p!=7&&valid3n(p,i,j,l)&&!isdeadN(p,i,j,l))return 1;
  char B[600]; memset(B,0,p+2); B[i]=B[j]=B[l]=1; return Gsep(p,B);}
/* copies */
#define MAXC 40000
static int ncp; static int cpK[MAXC],cpP[MAXC]; static unsigned char (*inv)[300];
static void addcp(int k,int p,int *X){ if(p<3||p>=N)return; cpK[ncp]=k;cpP[ncp]=p; memset(inv[ncp],0,300);
  for(int i=0;i<p;i++)inv[ncp][X[i]]=i+1; ncp++; }
static int excB(int q,int nu,int s){ return !(q==2||q==4||q==8) && ((nu==1&&s==1)||(nu+1==q&&s==q)); }
static void buildcp(void){ int X[300]; ncp=0;
  for(int p=1;2*p<=N;p++){ for(int k=1;k<=p;k++)X[k-1]=k*(N+2)/(p+1); addcp(0,p,X);}
  for(int h=0;h<=1;h++)for(int p=1;h+2*p<=N+1;p++){ for(int r=1;r<=p;r++)X[r-1]=(r*N-h)/p; addcp(1,p,X);}
  for(int q=2;q<=12&&q<=N;q++)for(int s=1;s<=q;s++){ if(excB(q,N%q,s))continue; int p=(N+q-s)/q; for(int y=1;y<=p;y++)X[y-1]=(y-1)*q+s; addcp(2,p,X);}
  for(int q=2;q<=N;q++){ if((N+1)%q)continue; int p=N/q; for(int y=1;y<=p;y++)X[y-1]=y*q; addcp(3,p,X);}
  for(int h=0;h<=1;h++)for(int p=3;p<=N;p+=2)for(int c=2;2*c*p+1<=N+h;c++){ for(int r=1;r<p;r++)X[r-1]=(r*N-h)/p; X[p-1]=N-c; addcp(4,p,X);}
  if(N%2==0){int p=N/2; if(p%2==0&&p>=4){ X[0]=1; for(int y=2;y<=p;y++)X[y-1]=2*y; addcp(5,p,X);}}
}
static int transfer(int a,int b,int c){
  for(int t=0;t<ncp;t++){ int i=inv[t][a],j=inv[t][b],l=inv[t][c];
    if(i&&j&&l&&known(cpP[t],i,j,l))return 1;}
  return 0;}
int main(int argc,char**argv){
  N=atoi(argv[1]); int K=argc>2?atoi(argv[2]):2; onlyint=getenv("ONLYINT")!=NULL;
  inv=malloc(sizeof(*inv)*MAXC); buildcp();
  long tot=0,cG=0,cT=0,cS=0,cR=0; char B[600];
  for(int a=2;a<=N-1;a++)for(int b=a+1;b<=N-1;b++)for(int c=b+1;c<=N-1;c++){
    if(a+c>N+1)continue; tot++;
    memset(B,0,N+2); B[a]=B[b]=B[c]=1;
    if(Gsep(N,B)){cG++;continue;}
    if(transfer(a,b,c)||transfer(N+1-c,N+1-b,N+1-a)){cT++;continue;}
    if(GK(N,B,K)){cS++;continue;}
    cR++; printf("R %d %d %d %d\n",N,a,b,c);
  }
  printf("N=%d tot=%ld G=%ld T=%ld S=%ld resid=%ld\n",N,tot,cG,cT,cS,cR);
  return 0;}

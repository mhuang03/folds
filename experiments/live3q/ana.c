/* ana.c NMIN NMAX [verbose]: classify the valid, non-dead 3-sets {a<b<c} (canonical:
   a + c <= N + 1) of the N-strip by the first rule that proves them co-reachable:
     F   closed-form Theorem G (F3S)
     S1  Theorem G after one extra valid step
     T   transfer through Z(N,p) or a residue class (q <= 12 with chain, or multiples of q
         when q | N+1) whose preimage is a non-dead 3-set of the smaller strip
     S2  Theorem G after two extra valid steps
   and prints the remaining sets. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
static int N; static u64 L[70], R[70];
static int reachv(int m){int a=m-1,b=N-m;return a<b?a:b;}
static int imb(u64 S,int m){return __builtin_popcountll(S&L[m])-__builtin_popcountll(S&R[m]);}
static int inwardG(u64 B){ int maxneg=0,minpos=N+1;
  for(int m=1;m<=N;m++){ if(B>>(m-1)&1)continue; int I=imb(B,m); if(I<0&&m>maxneg)maxneg=m; if(I>0&&m<minpos)minpos=m;}
  return maxneg<minpos; }
static int gk(u64 S,int k){ if(inwardG(S))return 1; if(!k)return 0; for(int m=1;m<=N;m++){ if(S>>(m-1)&1)continue; if(imb(S,m)==0&&gk(S|1ull<<(m-1),k-1))return 1;} return 0;}
static int isdeadN(int n,int a,int b,int c){
  for(int j=2;4*j<=n+3;j++){ if(a==1&&b==2*j&&c==2*j+1)return 1; if(a==n-2*j&&b==n+1-2*j&&c==n)return 1;}
  if(n%2==1&&n>=7){int k[4]={1,2,n-1,n};int in=0;for(int i=0;i<4;i++)in+=(a==k[i])+(b==k[i])+(c==k[i]);if(in==3)return 1;}
  if(n==7&&a==1&&b==4&&c==7)return 1;
  return 0;}
static int F(int n,int a,int b,int c){
  return !(2*a+2<=b && c+3<=2*b) && !(b+2<=c && n+b+3<=2*c && (2*a+2<=b || 2*b+2<=n+a));}
static int Fsym(int n,int a,int b,int c){ if(2*b<=n+1)return F(n,a,b,c); return F(n,n+1-c,n+1-b,n+1-a);}
static int idx(int *X,int p,int v){for(int i=0;i<p;i++)if(X[i]==v)return i+1;return 0;}
static int ncp; static int cpN[4000]; static unsigned char cpX[4000][64]; static char cpName[4000][24];
static void addcp(int p,int *X,const char*nm){ if(p<3)return; cpN[ncp]=p; for(int i=0;i<p;i++)cpX[ncp][i]=X[i]; strcpy(cpName[ncp],nm); ncp++;
  /* mirror copy */ cpN[ncp]=p; for(int i=0;i<p;i++)cpX[ncp][i]=N+1-X[p-1-i]; sprintf(cpName[ncp],"m%s",nm); ncp++; }
static int useB=1,useSw=1,useY=1;
static void buildcp(void){ int X[70]; char nm[24]; ncp=0;
  for(int p=3;2*p<=N;p++){ for(int k=1;k<=p;k++)X[k-1]=k*(N+2)/(p+1); sprintf(nm,"Z%d",p); addcp(p,X,nm);}
  for(int q=2;q<=12;q++)for(int s=1;s<=q;s++){ int nu=N%q;
    int exc = !(q==2||q==4||q==8) && ((nu==1&&s==1)||(nu+1==q&&s==q));
    if(exc && !(s==q&&(N+1)%q==0))continue;
    int p=0; for(int x=s;x<=N;x+=q)X[p++]=x; sprintf(nm,"r%d/%d",s,q); addcp(p,X,nm);}
  if(useB) for(int h=0;h<=1;h++)for(int p=3;h+2*p<=N+1;p++){ for(int r=1;r<=p;r++)X[r-1]=(r*N-h)/p; sprintf(nm,"B%d,%d",p,h); addcp(p,X,nm);}
  if(useSw) for(int h=0;h<=1;h++)for(int p=3;p<=N;p+=2)for(int c=2;2*c*p+1<=N+h;c++){ for(int r=1;r<p;r++)X[r-1]=(r*N-h)/p; X[p-1]=N-c;
      /* sort */ for(int i=0;i<p;i++)for(int j=i+1;j<p;j++)if(X[j]<X[i]){int t=X[i];X[i]=X[j];X[j]=t;}
      sprintf(nm,"W%d,%d,%d",p,h,c); addcp(p,X,nm);}
  if(useY && N%4==0 && N>=8){ int n=N/2; X[0]=1; for(int y=2;y<=n;y++)X[y-1]=2*y; sprintf(nm,"Y"); addcp(n,X,nm);}
}
static int transfer(int a,int b,int c,char *why){
  for(int t=0;t<ncp;t++){ int p=cpN[t]; int i=0,j=0,k=0;
    for(int u=0;u<p;u++){int v=cpX[t][u]; if(v==a)i=u+1; else if(v==b)j=u+1; else if(v==c)k=u+1;}
    if(i&&j&&k){ int s[3]={i,j,k}; for(int x=0;x<3;x++)for(int y=x+1;y<3;y++)if(s[y]<s[x]){int tt=s[x];s[x]=s[y];s[y]=tt;}
      if(!isdeadN(p,s[0],s[1],s[2])){sprintf(why,"%s->(%d,%d,%d)",cpName[t],s[0],s[1],s[2]);return 1;}}}
  return 0;}
static unsigned char seen[70][70][70];
int main(int argc,char**argv){
  int n0=atoi(argv[1]),n1=atoi(argv[2]),verbose=argc>3?atoi(argv[3]):0;
  for(N=n0;N<=n1;N++){
    for(int m=1;m<=N;m++){int r=reachv(m);L[m]=R[m]=0;for(int d=1;d<=r;d++){L[m]|=1ull<<(m-d-1);R[m]|=1ull<<(m+d-1);}}
    memset(seen,0,sizeof seen); buildcp();
    int cnt[6]={0};
    for(int x=1;x<=N;x++)for(int y=1;y<=N;y++){ if(y==x)continue; u64 S1=1ull<<(x-1); if(imb(S1,y))continue;
      for(int z=1;z<=N;z++){ if(z==x||z==y)continue; u64 S2=S1|1ull<<(y-1); if(imb(S2,z))continue;
        int a=x,b=y,c=z,t; if(a>b){t=a;a=b;b=t;} if(b>c){t=b;b=c;c=t;} if(a>b){t=a;a=b;b=t;}
        if(a+c>N+1){int a2=N+1-c,b2=N+1-b,c2=N+1-a;a=a2;b=b2;c=c2;}
        if(seen[a][b][c])continue; seen[a][b][c]=1;
        if(isdeadN(N,a,b,c))continue;
        u64 B=(1ull<<(a-1))|(1ull<<(b-1))|(1ull<<(c-1));
        char why[64]="";
        if(Fsym(N,a,b,c)){cnt[0]++;continue;}
        if(gk(B,1)){cnt[1]++;continue;}
        if(transfer(a,b,c,why)){cnt[2]++; if(verbose>1)printf("T %d %d %d %d %s\n",N,a,b,c,why); continue;}
        if(gk(B,2)){cnt[3]++; if(verbose>1)printf("S2 %d %d %d %d\n",N,a,b,c);continue;}
        cnt[4]++; if(verbose)printf("left %d %d %d %d\n",N,a,b,c);
      }}
    printf("N=%d F=%d S1=%d T=%d S2=%d left=%d\n",N,cnt[0],cnt[1],cnt[2],cnt[3],cnt[4]); fflush(stdout);
  }
  return 0;}

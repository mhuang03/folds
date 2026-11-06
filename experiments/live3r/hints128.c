/* hints.c N [maxdepth]: for every sorted triple a < b < c of [N] that is valid, not dead and
   fails F3S, print one hint (the Lean checker Live3q.hintOK):
     T k p u v i j l     transfer through copy k (copyF/copyOK of Folds/Live3q.lean)
     S c2 m1 m2 ...       Theorem G (centre c2/2) after the valid steps m1, m2, ...
     W x1 x2 ...          an ordering of [N] \ {a,b,c} from scratch
   each prefixed by "+" (the triple itself) or "-" (its mirror image (N+1-c, N+1-b, N+1-a)).
   Output lines:  a b c sign hint...   Summary on stderr. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u64;
static int popc(u64 x){return __builtin_popcountll((uint64_t)x)+__builtin_popcountll((uint64_t)(x>>64));}
static int N; static u64 L[130], R[130], FULL;
static int reachN(int n,int m){int a=m-1,b=n-m;return a<b?a:b;}
static int imb(u64 S,int m){return popc(S&L[m])-popc(S&R[m]);}
/* imbalance of a small set in strip n (closed form, for preimages) */
static int imbn(int n,int *xs,int k,int m){int r=reachN(n,m),s=0;for(int i=0;i<k;i++){int x=xs[i];if(m-r<=x&&x<m)s++;if(m<x&&x<=m+r)s--;}return s;}
static int valid3n(int n,int a,int b,int c){int t[3]={a,b,c};int P[6][3]={{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
  for(int q=0;q<6;q++){int x=t[P[q][0]],y=t[P[q][1]],z=t[P[q][2]];int s1[1]={x},s2[2]={x,y};
    if(imbn(n,s1,1,y)==0&&imbn(n,s2,2,z)==0)return 1;}return 0;}
static int isdeadN(int n,int a,int b,int c){
  if(a==1&&b%2==0&&c==b+1&&4<=b&&2*b<=n+3)return 1;
  if(c==n&&b==a+1&&(n-a)%2==0&&4<=n-a&&2*(n-a)<=n+3&&a<n)return 1;
  if(n%2==1&&n>=7&&((a==1&&b==2&&(c==n-1||c==n))||(b==n-1&&c==n&&(a==1||a==2))))return 1;
  return 0;}
static int F(int n,int a,int b,int c){
  return !(2*a+2<=b && c+3<=2*b) && !(b+2<=c && n+b+3<=2*c && (2*a+2<=b || 2*b+2<=n+a));}
static int Fsym(int n,int a,int b,int c){ if(2*b<=n+1)return F(n,a,b,c); return F(n,n+1-c,n+1-b,n+1-a);}
/* copies */
static int ncp; static int cpK[6000],cpP[6000],cpU[6000],cpV[6000]; static unsigned char cpX[6000][128];
static void addcp(int k,int p,int u,int v,int *X){ if(p<3||p>=N||p==7)return; cpK[ncp]=k;cpP[ncp]=p;cpU[ncp]=u;cpV[ncp]=v; for(int i=0;i<p;i++)cpX[ncp][i]=X[i]; ncp++; }
static int excB(int q,int nu,int s){ return !(q==2||q==4||q==8) && ((nu==1&&s==1)||(nu+1==q&&s==q)); }
static void buildcp(void){ int X[130]; ncp=0;
  for(int p=1;2*p<=N;p++){ for(int k=1;k<=p;k++)X[k-1]=k*(N+2)/(p+1); addcp(0,p,0,0,X);}            /* Z */
  for(int h=0;h<=1;h++)for(int p=1;h+2*p<=N+1;p++){ for(int r=1;r<=p;r++)X[r-1]=(r*N-h)/p; addcp(1,p,h,0,X);} /* Beatty */
  for(int q=2;q<=12&&q<=N;q++)for(int s=1;s<=q;s++){ if(excB(q,N%q,s))continue; int p=(N+q-s)/q; for(int y=1;y<=p;y++)X[y-1]=(y-1)*q+s; addcp(2,p,q,s,X);}
  for(int q=2;q<=N;q++){ if((N+1)%q)continue; int p=N/q; for(int y=1;y<=p;y++)X[y-1]=y*q; addcp(3,p,q,0,X);}
  for(int h=0;h<=1;h++)for(int p=3;p<=N;p+=2)for(int c=2;2*c*p+1<=N+h;c++){ for(int r=1;r<p;r++)X[r-1]=(r*N-h)/p; X[p-1]=N-c; addcp(4,p,h,c,X);}
  if(N%2==0){int p=N/2; if(p%2==0&&p>=4){ X[0]=1; for(int y=2;y<=p;y++)X[y-1]=2*y; addcp(5,p,0,0,X);}}
}
static int transfer(int a,int b,int c,char *out){
  for(int t=0;t<ncp;t++){ int p=cpP[t]; int i=0,j=0,l=0;
    for(int u=0;u<p;u++){int v=cpX[t][u]; if(v==a)i=u+1; else if(v==b)j=u+1; else if(v==c)l=u+1;}
    if(i&&j&&l&&i<j&&j<l&&valid3n(p,i,j,l)&&!isdeadN(p,i,j,l)){sprintf(out,"T %d %d %d %d %d %d %d",cpK[t],p,cpU[t],cpV[t],i,j,l);return 1;}}
  return 0;}
static int centre(u64 B){ int maxneg=0,minpos=N+1;
  for(int m=1;m<=N;m++){ if(B>>(m-1)&1)continue; int I=imb(B,m); if(I<0&&m>maxneg)maxneg=m; if(I>0&&m<minpos)minpos=m;}
  return maxneg<minpos ? 2*maxneg+1 : -1; }
static int stk[130];
static int gk(u64 S,int k,int d){ if(centre(S)>=0){stk[d]=0;return d+1;} if(!k)return 0;
  for(int m=1;m<=N;m++){ if(S>>(m-1)&1)continue; if(imb(S,m)==0){ stk[d]=m; int r=gk(S|(u64)1<<(m-1),k-1,d+1); if(r)return r;}} return 0;}
/* DFS completion */
#define HB 22
static u64 *ht; static size_t hmask; static long nodes;
static int hfind(u64 s){size_t h=((((uint64_t)s)^((uint64_t)(s>>64)*0x9E3779B97F4A7C15ull))*0x9E3779B97F4A7C15ull)>>(64-HB);while(ht[h]){if(ht[h]==s)return 1;h=(h+1)&hmask;}return 0;}
static void hins(u64 s){size_t h=((((uint64_t)s)^((uint64_t)(s>>64)*0x9E3779B97F4A7C15ull))*0x9E3779B97F4A7C15ull)>>(64-HB);while(ht[h]){if(ht[h]==s)return;h=(h+1)&hmask;}ht[h]=s;}
static int ord[130], path[130], depth;
static int dfs(u64 S){
  if(S==FULL)return 1;
  if(++nodes>3000000)return 0;
  if(hfind(S))return 0;
  for(int i=0;i<N;i++){int m=ord[i]; if(S>>(m-1)&1)continue; if(imb(S,m)==0){path[depth++]=m; if(dfs(S|(u64)1<<(m-1)))return 1; depth--;}}
  hins(S);return 0;
}
static int witness(u64 B,char *out){
  for(int t=0;t<9;t++){
    double c = (t==0)? (N+1)/2.0 : (t==1? 1.0 : (t==2? N : (t==3? (N+1)/4.0 : (t==4? 3*(N+1)/4.0 : (t==5? (N+1)/3.0 : (t==6? 2*(N+1)/3.0 : (t==7? (N+1)/5.0 : 4*(N+1)/5.0)))))));
    for(int i=0;i<N;i++)ord[i]=i+1;
    for(int i=0;i<N;i++)for(int j=i+1;j<N;j++){double di=ord[i]-c,dj=ord[j]-c;if(di<0)di=-di;if(dj<0)dj=-dj;if(dj<di){int x=ord[i];ord[i]=ord[j];ord[j]=x;}}
    memset(ht,0,sizeof(u64)<<HB); nodes=0; depth=0;
    if(dfs(B)){ char *o=out; o+=sprintf(o,"W"); for(int i=depth-1;i>=0;i--)o+=sprintf(o," %d",path[i]); return 1;}
  }
  return 0;
}
int main(int argc,char**argv){
  N=atoi(argv[1]); int maxd=argc>2?atoi(argv[2]):3;
  FULL=(((u64)1<<N)-1);
  for(int m=1;m<=N;m++){int r=reachN(N,m);L[m]=R[m]=0;for(int d=1;d<=r;d++){L[m]|=(u64)1<<(m-d-1);R[m]|=(u64)1<<(m+d-1);}}
  ht=malloc(sizeof(u64)<<HB); hmask=((u64)1<<HB)-1;
  buildcp();
  int cnt[8]={0}; char out[1024];
  for(int a=1;a<=N;a++)for(int b=a+1;b<=N;b++)for(int c=b+1;c<=N;c++){
    if(!valid3n(N,a,b,c)||isdeadN(N,a,b,c)||Fsym(N,a,b,c))continue;
    int ma=N+1-c,mb=N+1-b,mc=N+1-a;
    u64 B=((u64)1<<(a-1))|((u64)1<<(b-1))|((u64)1<<(c-1));
    u64 MB=((u64)1<<(ma-1))|((u64)1<<(mb-1))|((u64)1<<(mc-1));
    if(transfer(a,b,c,out)){printf("%d %d %d + %s\n",a,b,c,out);cnt[0]++;continue;}
    if(transfer(ma,mb,mc,out)){printf("%d %d %d - %s\n",a,b,c,out);cnt[1]++;continue;}
    int done=0;
    for(int k=1;k<=maxd&&!done;k++){
      for(int side=0;side<2&&!done;side++){ u64 S=side?MB:B; int d=gk(S,k,0); if(d){
        u64 T=S; for(int i=0;i<d-1;i++)T|=(u64)1<<(stk[i]-1);
        char *o=out; o+=sprintf(o,"S %d",centre(T)); for(int i=0;i<d-1;i++)o+=sprintf(o," %d",stk[i]);
        printf("%d %d %d %c %s\n",a,b,c,side?'-':'+',out); cnt[2+(d-1>1?1:0)]++; done=1;}}
    }
    if(done)continue;
    if(!getenv("NOWIT")&&witness(B,out)){printf("%d %d %d + %s\n",a,b,c,out);cnt[4]++;continue;}
    printf("%d %d %d ? FAIL\n",a,b,c); cnt[5]++;
  }
  fprintf(stderr,"N=%d T=%d MT=%d S1=%d Sk=%d W=%d FAIL=%d\n",N,cnt[0],cnt[1],cnt[2],cnt[3],cnt[4],cnt[5]);
  return 0;}

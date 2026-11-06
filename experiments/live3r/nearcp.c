/* nearcp.c FILE: for the triples "N a b c" of FILE (sorted by N), look for NEAR COPIES:
   maps phi: [p] -> [N] (a standard copy, or a standard copy with one panel moved by +-1)
   that preserve the window relation for every stepping panel j outside a set E
   (Agree(j, y) for all y), with E inside the preimage D of the triple (or of its mirror).
   Then CoReach p D and an ordering of Y = [N] \ phi([p]) from scratch give CoReach N phi(D).
   Prints, per triple, the first near copy found (with D, E) and whether Y is co-reachable
   (DFS).  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 W;
static int N; static W Lm[130], Rm[130], FULL;
static int pc(W x){return __builtin_popcountll((unsigned long long)x)+__builtin_popcountll((unsigned long long)(x>>64));}
static int reachn(int n,int m){int a=m-1,b=n-m;return a<b?a:b;}
static int imb(W S,int m){return pc(S&Lm[m])-pc(S&Rm[m]);}
static int isdeadN(int n,int a,int b,int c){
  if(a==1&&b%2==0&&c==b+1&&4<=b&&2*b<=n+3)return 1;
  if(c==n&&b==a+1&&(n-a)%2==0&&4<=n-a&&2*(n-a)<=n+3&&a<n)return 1;
  if(n%2==1&&n>=7&&((a==1&&b==2&&(c==n-1||c==n))||(b==n-1&&c==n&&(a==1||a==2))))return 1;
  if(n==7&&a==1&&b==4&&c==7)return 1;
  return 0;}
static int imbn(int n,int *xs,int k,int m){int r=reachn(n,m),s=0;for(int i=0;i<k;i++){int x=xs[i];if(m-r<=x&&x<m)s++;if(m<x&&x<=m+r)s--;}return s;}
static int valid3n(int n,int a,int b,int c){int t[3]={a,b,c};int P[6][3]={{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
  for(int q=0;q<6;q++){int x=t[P[q][0]],y=t[P[q][1]],z=t[P[q][2]];int s1[1]={x},s2[2]={x,y};
    if(imbn(n,s1,1,y)==0&&imbn(n,s2,2,z)==0)return 1;}return 0;}
/* relation of y to j in strip n: 1 left arm, -1 right arm, 0 outside */
static int rel(int n,int j,int y){int r=reachn(n,j); if(j-r<=y&&y<j)return 1; if(j<y&&y<=j+r)return -1; return 0;}
#define HB 22
static W *ht; static size_t hmask; static long nodes;
static size_t hh(W s){unsigned long long a=(unsigned long long)s,b=(unsigned long long)(s>>64);return ((a^(b*0x9E3779B97F4A7C15ull))*0x9E3779B97F4A7C15ull)>>(64-HB);}
static int hfind(W s){size_t h=hh(s);while(ht[h]){if(ht[h]==s)return 1;h=(h+1)&hmask;}return 0;}
static void hins(W s){size_t h=hh(s);while(ht[h]){if(ht[h]==s)return;h=(h+1)&hmask;}ht[h]=s;}
static int ord[130];
static int dfs(W S){ if(S==FULL)return 1; if(++nodes>2000000)return 0; if(hfind(S))return 0;
  for(int i=0;i<N;i++){int m=ord[i]; if((S>>(m-1))&1)continue; if(imb(S,m)==0){ if(dfs(S|((W)1<<(m-1))))return 1;}}
  hins(S);return 0;}
static int inwardG(W B){ int maxneg=0,minpos=N+1;
  for(int m=1;m<=N;m++){ if((B>>(m-1))&1)continue; int I=imb(B,m); if(I<0&&m>maxneg)maxneg=m; if(I>0&&m<minpos)minpos=m;}
  return maxneg<minpos; }
static int gk(W S,int k){ if(inwardG(S))return 1; if(!k)return 0; for(int m=1;m<=N;m++){ if((S>>(m-1))&1)continue; if(imb(S,m)==0&&gk(S|((W)1<<(m-1)),k-1))return 1;} return 0;}
static int coreach(W B){ /* 1 yes, 0 unknown */
  if(getenv("YINW")){ int k=atoi(getenv("YINW"))-1; return gk(B,k); }
  for(int t=0;t<5;t++){ double c=(t==0)?(N+1)/2.0:(t==1?1:(t==2?N:(t==3?(N+1)/4.0:3*(N+1)/4.0)));
    for(int i=0;i<N;i++)ord[i]=i+1;
    for(int i=0;i<N;i++)for(int j=i+1;j<N;j++){double di=ord[i]-c,dj=ord[j]-c;if(di<0)di=-di;if(dj<0)dj=-dj;if(dj<di){int x=ord[i];ord[i]=ord[j];ord[j]=x;}}
    memset(ht,0,sizeof(W)<<HB); nodes=0; if(dfs(B))return 1; }
  return 0;}
/* maps */
#define MAXM 200000
static int nm, mp[MAXM]; static unsigned char mX[MAXM][128]; static char mname[MAXM][40]; static W mE[MAXM];
static void addmap(int p,int *X,const char*nm0){
  if(p<3||p>=N||p==7||nm>=MAXM)return;
  for(int i=0;i+1<p;i++)if(X[i]>=X[i+1])return;
  if(X[0]<1||X[p-1]>N)return;
  W E=0; int ne=0;
  for(int j=1;j<=p;j++){ for(int y=1;y<=p;y++){ if(y==j)continue; if(rel(N,X[j-1],X[y-1])!=rel(p,j,y)){E|=(W)1<<(j-1);ne++;break;} } if(ne>3)return; }
  mp[nm]=p; for(int i=0;i<p;i++)mX[nm][i]=X[i]; strcpy(mname[nm],nm0); mE[nm]=E; nm++; }
static void addvar(int p,int *X,const char*nm0){ char nm1[40]; int Y[128];
  addmap(p,X,nm0);
  int mv=getenv("MOVES")?atoi(getenv("MOVES")):1;
  for(int i=0;i<p;i++)for(int d=-1;d<=1;d+=2){ memcpy(Y,X,sizeof(int)*p); Y[i]+=d; sprintf(nm1,"%s@%d%+d",nm0,i+1,d); addmap(p,Y,nm1);
    if(mv>=2) for(int i2=i+1;i2<p;i2++)for(int d2=-1;d2<=1;d2+=2){ int Z2[128]; memcpy(Z2,Y,sizeof(int)*p); Z2[i2]+=d2; sprintf(nm1,"%s@%d%+d@%d%+d",nm0,i+1,d,i2+1,d2); addmap(p,Z2,nm1);} } }
static void addboth(int p,int *X,const char*nm0){ int Y[128]; char nm1[40]; addvar(p,X,nm0);
  for(int i=0;i<p;i++)Y[i]=N+1-X[p-1-i]; sprintf(nm1,"m%s",nm0); addvar(p,Y,nm1); }
static void buildmaps(void){ int X[130]; char nmm[40]; nm=0;
  int maxq=getenv("MAXQ")?atoi(getenv("MAXQ")):12, noz=getenv("NOZB")!=0;
  for(int q=2;q<=maxq;q++)for(int s=1;s<=q;s++){ int p=0; for(int x=s;x<=N;x+=q)X[p++]=x; sprintf(nmm,"r%d/%d",s,q); addboth(p,X,nmm);}
  if(getenv("CHIX")&&N%2==1){ int p=0; X[p++]=1; for(int x=4;x<=N-3;x+=2)X[p++]=x; X[p++]=N; addboth(p,X,"chiX"); }
  if(noz)return;
  for(int p=3;2*p<=N;p++){ for(int k=1;k<=p;k++)X[k-1]=k*(N+2)/(p+1); sprintf(nmm,"Z%d",p); addboth(p,X,nmm);}
  for(int h=0;h<=1;h++)for(int p=3;h+2*p<=N+1;p++){ for(int r=1;r<=p;r++)X[r-1]=(r*N-h)/p; sprintf(nmm,"B%d,%d",p,h); addboth(p,X,nmm);}
}
static int ycache[MAXM];
int main(int argc,char**argv){
  FILE *f=fopen(argv[1],"r"); int n,a,b,c; int curN=-1;
  ht=malloc(sizeof(W)<<HB); hmask=((size_t)1<<HB)-1;
  int tot=0,cov=0;
  while(fscanf(f,"%d %d %d %d",&n,&a,&b,&c)==4){
    if(n!=curN){ curN=n; N=n; FULL=(N==128)?~(W)0:(((W)1<<N)-1);
      for(int m=1;m<=N;m++){int r=reachn(N,m);Lm[m]=Rm[m]=0;for(int d=1;d<=r;d++){Lm[m]|=(W)1<<(m-d-1);Rm[m]|=(W)1<<(m+d-1);}}
      buildmaps(); for(int i=0;i<nm;i++)ycache[i]=-1; }
    tot++; int found=0;
    for(int side=0;side<2&&!found;side++){ int t[3]; if(side==0){t[0]=a;t[1]=b;t[2]=c;}else{t[0]=N+1-c;t[1]=N+1-b;t[2]=N+1-a;}
      for(int k=0;k<nm&&!found;k++){ int p=mp[k]; int pre[3]={0,0,0};
        for(int u=0;u<p;u++)for(int s=0;s<3;s++)if(mX[k][u]==t[s])pre[s]=u+1;
        if(!pre[0]||!pre[1]||!pre[2])continue;
        W D=((W)1<<(pre[0]-1))|((W)1<<(pre[1]-1))|((W)1<<(pre[2]-1));
        if(mE[k]&~D)continue;
        if(!valid3n(p,pre[0],pre[1],pre[2])||isdeadN(p,pre[0],pre[1],pre[2]))continue;
        if(ycache[k]<0){ W I=0; for(int u=0;u<p;u++)I|=(W)1<<(mX[k][u]-1); ycache[k]=coreach(I);}
        if(!ycache[k])continue;
        printf("%d %d %d %d %c %s p=%d D=(%d,%d,%d)\n",N,a,b,c,side?'-':'+',mname[k],p,pre[0],pre[1],pre[2]); found=1; }
    }
    if(found)cov++; else printf("%d %d %d %d LEFT\n",N,a,b,c);
    fflush(stdout);
  }
  fprintf(stderr,"total %d covered %d\n",tot,cov);
  return 0;}

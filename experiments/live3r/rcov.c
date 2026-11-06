/* rcov.c FILE [K]: for the triples "N a b c" of FILE (sorted by N; residual lists of
   resid128.py), find a hint for the new rules of Folds/Live3r.lean:
     X i j l                       chiX transfer (N = 2n - 1 odd), preimage (i, j, l) in [n-1]
     R k p u v y1 e1 y2 e2 i j l c2 ms...   the near-copy rule nearTrB (moves e = 1: +1,
                                   e = 2: -1, y = 0: no move; Y by Theorem G after the steps ms)
   for the triple ("+") or its mirror image ("-"); else LEFT.  Moves only on the panels of
   the preimage.  K = maximal number of steps for the image (default 2). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 W;
static int N; static W Lm[130], Rm[130];
static int pc(W x){return __builtin_popcountll((unsigned long long)x)+__builtin_popcountll((unsigned long long)(x>>64));}
static int reachn(int n,int m){int a=m-1,b=n-m;return a<b?a:b;}
static int imb(W S,int m){return pc(S&Lm[m])-pc(S&Rm[m]);}
static int isdeadN(int n,int a,int b,int c){
  if(a==1&&b%2==0&&c==b+1&&4<=b&&2*b<=n+3)return 1;
  if(c==n&&b==a+1&&(n-a)%2==0&&4<=n-a&&2*(n-a)<=n+3&&a<n)return 1;
  if(n%2==1&&n>=7&&((a==1&&b==2&&(c==n-1||c==n))||(b==n-1&&c==n&&(a==1||a==2))))return 1;
  return 0;}
static int imbn(int n,int *xs,int k,int m){int r=reachn(n,m),s=0;for(int i=0;i<k;i++){int x=xs[i];if(m-r<=x&&x<m)s++;if(m<x&&x<=m+r)s--;}return s;}
static int valid3n(int n,int a,int b,int c){int t[3]={a,b,c};int P[6][3]={{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
  for(int q=0;q<6;q++){int x=t[P[q][0]],y=t[P[q][1]],z=t[P[q][2]];int s1[1]={x},s2[2]={x,y};
    if(imbn(n,s1,1,y)==0&&imbn(n,s2,2,z)==0)return 1;}return 0;}
static int okpre(int p,int i,int j,int l){ return p<N && p!=7 && 1<=i && i<j && j<l && l<=p && valid3n(p,i,j,l) && !isdeadN(p,i,j,l); }
static int rel(int n,int j,int y){int r=reachn(n,j); if(j-r<=y&&y<j)return 1; if(j<y&&y<=j+r)return -1; return 0;}
static int centre(W B){ int maxneg=0,minpos=N+1;
  for(int m=1;m<=N;m++){ if((B>>(m-1))&1)continue; int I=imb(B,m); if(I<0&&m>maxneg)maxneg=m; if(I>0&&m<minpos)minpos=m;}
  return maxneg<minpos ? 2*maxneg+1 : -1; }
static int stk[10];
static int gk(W S,int k,int d){ int c=centre(S); if(c>=0){stk[d]=c;return d+1;} if(!k)return 0;
  for(int m=1;m<=N;m++){ if((S>>(m-1))&1)continue; if(imb(S,m)==0){ stk[d]=m; int r=gk(S|((W)1<<(m-1)),k-1,d+1); if(r)return r;}} return 0;}
/* cache of image sets -> steps */
#define HC 65536
static W ck[HC]; static int cv[HC]; static char cs[HC][64]; static int cused[HC];
static int K=2;
static int ycheck(W B,char *out){ unsigned long long h=((unsigned long long)B ^ (unsigned long long)(B>>64)*0x9E3779B97F4A7C15ull)*0x9E3779B97F4A7C15ull; int s=h>>48;
  while(cused[s]&&ck[s]!=B)s=(s+1)&(HC-1);
  if(!cused[s]){ cused[s]=1; ck[s]=B; int d=gk(B,K,0); cv[s]=d; if(d){ char *o=cs[s]; o+=sprintf(o,"%d",stk[d-1]); for(int i=0;i<d-1;i++)o+=sprintf(o," %d",stk[i]); } }
  if(cv[s])strcpy(out,cs[s]); return cv[s]; }
/* bases: copyF k N p u v */
static int nb, bk[2000],bp[2000],bu[2000],bv[2000]; static unsigned char bX[2000][128];
static void addb(int k,int p,int u,int v,int *X){ if(p<3||p>=N||p==7||nb>=2000)return; bk[nb]=k;bp[nb]=p;bu[nb]=u;bv[nb]=v; for(int i=0;i<p;i++)bX[nb][i]=X[i]; nb++; }
static void buildb(void){ int X[130]; nb=0;
  for(int p=1;p<N;p++){ for(int k=1;k<=p;k++)X[k-1]=k*(N+2)/(p+1); if(X[p-1]<=N)addb(0,p,0,0,X);}
  for(int h=0;h<=1;h++)for(int p=1;p<N;p++){ int ok=1; for(int r=1;r<=p;r++){X[r-1]=(r*N-h)/p; if(X[r-1]<1)ok=0;} if(ok)addb(1,p,h,0,X);}
  for(int q=2;q<=N/2;q++)for(int s=1;s<=q;s++){ int p=(N+q-s)/q; for(int y=1;y<=p;y++)X[y-1]=(y-1)*q+s; addb(2,p,q,s,X);}
}
static int phi[130];
static int YPSI=0, NOY=0;
/* Y = complement of the image I: as the increasing image of [q]; irregular panels of psi must form
   a live prefix: one panel (any), or two panels (i1, i2) valid in [q] and in [N], non-dead pair */
static int deadpair(int n,int u,int v){ return u==1&&v==n&&((n%2==0&&n>=4)||n==7); }
static int ypsi(W I,char *out){ int ps[130],q=0; for(int x=1;x<=N;x++) if(!((I>>(x-1))&1)) ps[++q]=x;
  if(q<1)return 0; int irr[4],ni=0;
  for(int i=1;i<=q;i++){ int bad=0; for(int y=1;y<=q;y++) if(rel(N,ps[i],ps[y])!=rel(q,i,y)){bad=1;break;} if(bad){ if(ni>=2)return 0; irr[ni++]=i; } }
  if(ni<=1){ for(int i1=1;i1<=q;i1++)for(int i2=1;i2<=q;i2++){ if(i1==i2)continue; if(ni==1&&i1!=irr[0]&&i2!=irr[0])continue;
      if(rel(q,i2,i1)!=0||rel(N,ps[i2],ps[i1])!=0)continue; int u=i1<i2?i1:i2,v=i1<i2?i2:i1; if(deadpair(q,u,v))continue;
      sprintf(out,"P %d %d",i1,i2); return 1; } return 0; }
  for(int o=0;o<2;o++){ int i1=irr[o],i2=irr[1-o];
    if(rel(q,i2,i1)!=0)continue;            /* i2 valid after [i1] in [q] */
    if(rel(N,ps[i2],ps[i1])!=0)continue;    /* and in [N] */
    int u=i1<i2?i1:i2,v=i1<i2?i2:i1; if(deadpair(q,u,v))continue;
    sprintf(out,"P %d %d",i1,i2); return 1; }
  return 0; }
static int regall(int p,int i,int j,int l){
  for(int x=1;x<=p;x++){ if(x==i||x==j||x==l)continue;
    for(int y=1;y<=p;y++) if(rel(N,phi[x],phi[y])!=rel(p,x,y)) return 0; }
  return 1;}
static int tryt(int a,int b,int c,char *out){
  int t[3]={a,b,c};
  for(int q=0;q<nb;q++){ int p=bp[q];
    /* candidates for each target: (index, e) */
    int ci[3][3],ce[3][3],nc[3];
    for(int s=0;s<3;s++){ nc[s]=0;
      for(int y=1;y<=p;y++){ int x=bX[q][y-1];
        if(x==t[s]){ci[s][nc[s]]=y;ce[s][nc[s]]=0;nc[s]++;}
        else if(x+1==t[s]){ci[s][nc[s]]=y;ce[s][nc[s]]=1;nc[s]++;}
        else if(x-1==t[s]){ci[s][nc[s]]=y;ce[s][nc[s]]=2;nc[s]++;} } }
    for(int A=0;A<nc[0];A++)for(int B=0;B<nc[1];B++)for(int C=0;C<nc[2];C++){
      int ii=ci[0][A],jj=ci[1][B],ll=ci[2][C]; int nmv=(ce[0][A]>0)+(ce[1][B]>0)+(ce[2][C]>0);
      if(nmv>2)continue; if(!okpre(p,ii,jj,ll))continue;
      for(int y=1;y<=p;y++)phi[y]=bX[q][y-1];
      int y1=0,e1=0,y2=0,e2=0; int idx[3]={ii,jj,ll}, ee[3]={ce[0][A],ce[1][B],ce[2][C]};
      for(int s=0;s<3;s++) if(ee[s]){ if(!y1){y1=idx[s];e1=ee[s];} else {y2=idx[s];e2=ee[s];} phi[idx[s]]+= (ee[s]==1?1:-1); }
      int inc=1; for(int y=1;y<=p;y++){ if(phi[y]<1||phi[y]>N)inc=0; if(y<p&&phi[y]>=phi[y+1])inc=0;} if(!inc)continue;
      if(!regall(p,ii,jj,ll)){ if(getenv("DBG")){ printf("  irr k=%d p=%d u=%d v=%d D=(%d,%d,%d) mv=%d,%d %d,%d irregular:",bk[q],p,bu[q],bv[q],ii,jj,ll,y1,e1,y2,e2);
          for(int x=1;x<=p;x++){ if(x==ii||x==jj||x==ll)continue; for(int y=1;y<=p;y++) if(rel(N,phi[x],phi[y])!=rel(p,x,y)){printf(" %d(vs %d)",x,y);break;} } printf("\n"); } continue;}
      W I=0; for(int y=1;y<=p;y++)I|=(W)1<<(phi[y]-1);
      char so[64]; if(NOY){ sprintf(so,"NOY"); } else if(!ycheck(I,so)){ if(!YPSI||!ypsi(I,so))continue; }
      sprintf(out,"R %d %d %d %d %d %d %d %d %d %d %d %s",bk[q],p,bu[q],bv[q],y1,e1,y2,e2,ii,jj,ll,so); return 1; }
  }
  return 0;}
static int tryx(int a,int b,int c,char *out){
  if(N%2==0)return 0; int n=(N+1)/2; if(n<6||n==7)return 0;
  int t[3]={a,b,c},pre[3];
  for(int s=0;s<3;s++){ int x=t[s]; if(x==1)pre[s]=1; else if(x==N)pre[s]=n-1; else if(x%2==0&&x>=4&&x<=N-3)pre[s]=x/2; else return 0; }
  if(!okpre(n-1,pre[0],pre[1],pre[2]))return 0;
  sprintf(out,"X %d %d %d",pre[0],pre[1],pre[2]); return 1; }
int main(int argc,char**argv){
  FILE *f=fopen(argv[1],"r"); if(argc>2)K=atoi(argv[2]); YPSI=getenv("YPSI")!=0; NOY=getenv("NOY")!=0; int n,a,b,c,curN=-1,tot=0,cov=0;
  while(fscanf(f,"%d %d %d %d",&n,&a,&b,&c)==4){
    if(n!=curN){ curN=n; N=n; memset(cused,0,sizeof cused);
      for(int m=1;m<=N;m++){int r=reachn(N,m);Lm[m]=Rm[m]=0;for(int d=1;d<=r;d++){Lm[m]|=(W)1<<(m-d-1);Rm[m]|=(W)1<<(m+d-1);}}
      buildb(); }
    tot++; char out[256]; int found=0;
    for(int side=0;side<2&&!found;side++){ int x,y,z; if(!side){x=a;y=b;z=c;}else{x=N+1-c;y=N+1-b;z=N+1-a;}
      if(tryx(x,y,z,out)||tryt(x,y,z,out)){ printf("%d %d %d %d %c %s\n",N,a,b,c,side?'-':'+',out); found=1; } }
    if(found)cov++; else printf("%d %d %d %d LEFT\n",N,a,b,c);
    fflush(stdout); }
  fprintf(stderr,"total %d covered %d\n",tot,cov);
  return 0;}

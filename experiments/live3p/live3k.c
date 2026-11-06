/* live3.c: valid 3-prefix sets of the N-strip.  For each set B = set of a valid 3-prefix:
   dead-list membership (D_j, mirrors, odd-N corners), Theorem G criterion (Inward for some
   centre), and a completion witness (DFS from background B, memo of failed states).
   Usage: live3 N [verbose]   Output: summary line, plus "nonG" / "nowit" lines. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
static int N; static u64 L[70], R[70], FULL;
static int reachv(int m){int a=m-1,b=N-m;return a<b?a:b;}
static int imb(u64 S,int m){return __builtin_popcountll(S&L[m])-__builtin_popcountll(S&R[m]);}
#define HB 24
static u64 *ht; static size_t hmask; static long nodes, limit;
static int hfind(u64 s){size_t h=(s*0x9E3779B97F4A7C15ull)>>(64-HB);while(ht[h]){if(ht[h]==s)return 1;h=(h+1)&hmask;}return 0;}
static void hins(u64 s){size_t h=(s*0x9E3779B97F4A7C15ull)>>(64-HB);while(ht[h]){if(ht[h]==s)return;h=(h+1)&hmask;}ht[h]=s;}
static int ord[70];
static int dfs(u64 S){
  if(S==FULL)return 1;
  if(++nodes>limit)return 0;
  if(hfind(S))return 0;
  for(int i=0;i<N;i++){int m=ord[i]; if(S>>(m-1)&1)continue; if(imb(S,m)==0&&dfs(S|1ull<<(m-1)))return 1;}
  hins(S);return 0;
}
static int witness(u64 B){
  for(int t=0;t<5;t++){
    double c = (t==0)? (N+1)/2.0 : (t==1? 1.0 : (t==2? N : (t==3? (N+1)/4.0 : 3*(N+1)/4.0)));
    for(int i=0;i<N;i++)ord[i]=i+1;
    for(int i=0;i<N;i++)for(int j=i+1;j<N;j++){double di=ord[i]-c,dj=ord[j]-c;if(di<0)di=-di;if(dj<0)dj=-dj;if(dj<di){int x=ord[i];ord[i]=ord[j];ord[j]=x;}}
    memset(ht,0,sizeof(u64)<<HB); nodes=0; limit=2000000;
    if(dfs(B))return 1;
  }
  return 0;
}
static int inwardG(u64 B){ int maxneg=0,minpos=N+1;
  for(int m=1;m<=N;m++){ if(B>>(m-1)&1)continue; int I=imb(B,m); if(I<0&&m>maxneg)maxneg=m; if(I>0&&m<minpos)minpos=m;}
  return maxneg<minpos; }
static int gk(u64 S,int k){ if(inwardG(S))return 1; if(!k)return 0; for(int m=1;m<=N;m++){ if(S>>(m-1)&1)continue; if(imb(S,m)==0&&gk(S|1ull<<(m-1),k-1))return 1;} return 0;}
static int isdead(int a,int b,int c){ /* a<b<c */
  for(int j=2;4*j<=N+3;j++){ if(a==1&&b==2*j&&c==2*j+1)return 1; if(a==N-2*j&&b==N+1-2*j&&c==N)return 1;}
  if(N%2==1&&N>=5){int k[4]={1,2,N-1,N};int in=0;for(int i=0;i<4;i++)in+=(a==k[i])+(b==k[i])+(c==k[i]);if(in==3)return 1;}
  return 0;}
static int hist[10];
static unsigned char seen[70][70][70];
int main(int argc,char**argv){
  N=atoi(argv[1]); int verbose=argc>2;
  FULL=(N==64)?~0ull:((1ull<<N)-1);
  for(int m=1;m<=N;m++){int r=reachv(m);L[m]=R[m]=0;for(int d=1;d<=r;d++){L[m]|=1ull<<(m-d-1);R[m]|=1ull<<(m+d-1);}}
  ht=malloc(sizeof(u64)<<HB); hmask=(1ull<<HB)-1;
  int nsets=0,ndead=0,nG=0,nwit=0,nbad=0,ndeadwit=0,npref=0,ndpref=0;
  for(int x=1;x<=N;x++)for(int y=1;y<=N;y++){ if(y==x)continue; u64 S1=1ull<<(x-1); if(imb(S1,y))continue;
    for(int z=1;z<=N;z++){ if(z==x||z==y)continue; u64 S2=S1|1ull<<(y-1); if(imb(S2,z))continue;
      int a=x,b=y,c=z,t; if(a>b){t=a;a=b;b=t;} if(b>c){t=b;b=c;c=t;} if(a>b){t=a;a=b;b=t;}
      npref++; if(isdead(a,b,c))ndpref++;
      if(seen[a][b][c])continue; seen[a][b][c]=1; nsets++;
      u64 B=S2|1ull<<(z-1);
      int d=isdead(a,b,c), g=inwardG(B);
      if(d){ndead++; if(verbose && N<=22 && witness(B)){ndeadwit++;printf("DEADWIT %d %d %d %d\n",N,a,b,c);} continue;}
      if(g){nG++; continue;}
      int kk=-1; for(int k=1;k<=3;k++) if(gk(B,k)){kk=k;break;} hist[kk+1]++; if(verbose>0&&kk<0)printf("noGk %d %d %d %d\n",N,a,b,c);
      int w=witness(B); if(w)nwit++; else {nbad++;printf("nowit %d %d %d %d\n",N,a,b,c);}
      if(verbose>1)printf("nonG %d %d %d %d\n",N,a,b,c);
    }}
  printf("summary N=%d prefixes=%d deadprefixes=%d sets=%d dead=%d inwardG=%d witnessed=%d unresolved=%d deadwit=%d\n",N,npref,ndpref,nsets,ndead,nG,nwit,nbad,ndeadwit);
  printf("hist none=%d k1=%d k2=%d k3=%d\n",hist[0],hist[2],hist[3],hist[4]);
  return 0;
}

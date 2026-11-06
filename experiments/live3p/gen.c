/* gen.c: witness orderings for the Lean certificate (Folds/Live3p.lean, cover3).
   For each valid 3-prefix set {a<b<c} of the N-strip that is not dead and does not satisfy
   the closed-form Theorem G criterion F (inward3.py), take the canonical representative
   (the set itself if a + c <= N + 1, else its mirror image) and print a semi-symmetric
   ordering of [N] \ {a,b,c} FROM SCRATCH:   W N a b c w_1 ... w_{N-3}
   (found as a completion after the background {a,b,c}, read backwards; re-verified here).
   Usage: gen N */
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
static int ord[70], path[70], plen;
static int dfs(u64 S){
  if(S==FULL)return 1;
  if(++nodes>limit)return 0;
  if(hfind(S))return 0;
  for(int i=0;i<N;i++){int m=ord[i]; if(S>>(m-1)&1)continue;
    if(imb(S,m)==0){path[plen++]=m; if(dfs(S|1ull<<(m-1)))return 1; plen--;}}
  hins(S);return 0;
}
static int witness(u64 B){
  for(int t=0;t<5;t++){
    double c = (t==0)? (N+1)/2.0 : (t==1? 1.0 : (t==2? N : (t==3? (N+1)/4.0 : 3*(N+1)/4.0)));
    for(int i=0;i<N;i++)ord[i]=i+1;
    for(int i=0;i<N;i++)for(int j=i+1;j<N;j++){double di=ord[i]-c,dj=ord[j]-c;if(di<0)di=-di;if(dj<0)dj=-dj;if(dj<di){int x=ord[i];ord[i]=ord[j];ord[j]=x;}}
    memset(ht,0,sizeof(u64)<<HB); nodes=0; limit=4000000; plen=0;
    if(dfs(B))return 1;
  }
  return 0;
}
static int isdead(int a,int b,int c){
  for(int j=2;4*j<=N+3;j++){ if(a==1&&b==2*j&&c==2*j+1)return 1; if(a==N-2*j&&b==N+1-2*j&&c==N)return 1;}
  if(N%2==1&&N>=7){int k[4]={1,2,N-1,N};int in=0;for(int i=0;i<4;i++)in+=(a==k[i])+(b==k[i])+(c==k[i]);if(in==3)return 1;}
  return 0;}
static int F3(int a,int b,int c){
  return !(2*a+2<=b && c+3<=2*b) && !(b+2<=c && N+b+3<=2*c && (2*a+2<=b || 2*b+2<=N+a));}
static int Fsym(int a,int b,int c){ return 2*b<=N+1 ? F3(a,b,c) : F3(N+1-c,N+1-b,N+1-a); }
static unsigned char seen[70][70][70];
int main(int argc,char**argv){
  N=atoi(argv[1]);
  FULL=(1ull<<N)-1;
  for(int m=1;m<=N;m++){int r=reachv(m);L[m]=R[m]=0;for(int d=1;d<=r;d++){L[m]|=1ull<<(m-d-1);R[m]|=1ull<<(m+d-1);}}
  ht=malloc(sizeof(u64)<<HB); hmask=(1ull<<HB)-1;
  int bad=0;
  for(int x=1;x<=N;x++)for(int y=1;y<=N;y++){ if(y==x)continue; u64 S1=1ull<<(x-1); if(imb(S1,y))continue;
    for(int z=1;z<=N;z++){ if(z==x||z==y)continue; u64 S2=S1|1ull<<(y-1); if(imb(S2,z))continue;
      int a=x,b=y,c=z,t; if(a>b){t=a;a=b;b=t;} if(b>c){t=b;b=c;c=t;} if(a>b){t=a;a=b;b=t;}
      if(isdead(a,b,c)||Fsym(a,b,c))continue;
      if(a+c>N+1){int a2=N+1-c,b2=N+1-b,c2=N+1-a;a=a2;b=b2;c=c2;}
      if(seen[a][b][c])continue; seen[a][b][c]=1;
      u64 B=(1ull<<(a-1))|(1ull<<(b-1))|(1ull<<(c-1));
      if(!witness(B)){bad++;fprintf(stderr,"nowit %d %d %d %d\n",N,a,b,c);continue;}
      /* verify the reversed path from scratch */
      u64 S=0; int ok=(plen==N-3);
      for(int i=plen-1;i>=0;i--){int m=path[i]; if((S|B)>>(m-1)&1)ok=0; if(imb(S,m))ok=0; S|=1ull<<(m-1);}
      if(!ok||(S|B)!=FULL){bad++;fprintf(stderr,"badwit %d %d %d %d\n",N,a,b,c);continue;}
      printf("W %d %d %d %d",N,a,b,c); for(int i=plen-1;i>=0;i--)printf(" %d",path[i]); printf("\n");
    }}
  if(bad){fprintf(stderr,"N=%d bad=%d\n",N,bad);return 1;}
  return 0;
}

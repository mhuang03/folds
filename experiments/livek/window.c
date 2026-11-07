/* window.c: how central must a k-set be to be co-reachable?
   centrality(D) = min(min D, N+1-max D).  For t = ceil(N/3), t-1, t-2, ... count the k-subsets
   D of [N] with centrality exactly t that fail Theorem G, and those for which no completion
   is found (G, G after one valid step, or DFS from the background D).
   Stops at the first level with an unresolved set.  Usage: window N k */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
static int N, K; static u64 L[70], R[70], FULL;
static int reachv(int m){int a=m-1,b=N-m;return a<b?a:b;}
static int imb(u64 S,int m){return __builtin_popcountll(S&L[m])-__builtin_popcountll(S&R[m]);}
#define HB 22
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
    memset(ht,0,sizeof(u64)<<HB); nodes=0; limit=300000;
    if(dfs(B))return 1;
  }
  return 0;
}
static int inwardG(u64 B){ int maxneg=0,minpos=N+1;
  for(int m=1;m<=N;m++){ if(B>>(m-1)&1)continue; int I=imb(B,m); if(I<0&&m>maxneg)maxneg=m; if(I>0&&m<minpos)minpos=m;}
  return maxneg<minpos; }
static int g1(u64 S){ for(int m=1;m<=N;m++){ if(S>>(m-1)&1)continue; if(imb(S,m)==0&&inwardG(S|1ull<<(m-1)))return 1;} return 0;}
static long nset,nnotG,nunres; static int T; static int firstbad[8];
static void enumsets(u64 S,int start,int depth,int hi){
  if(depth==K){ int mn=__builtin_ctzll(S)+1, mx=64-__builtin_clzll(S); int c=mn<N+1-mx?mn:N+1-mx; if(c!=T)return;
    nset++; if(inwardG(S))return; nnotG++; if(g1(S)||witness(S))return; nunres++;
    if(nunres<=3){int j=0;for(int m=1;m<=N;m++)if(S>>(m-1)&1)firstbad[j++]=m;printf("  unresolved:");for(int i=0;i<K;i++)printf(" %d",firstbad[i]);printf("\n");}
    return;}
  for(int m=start;m<=hi;m++)enumsets(S|1ull<<(m-1),m+1,depth+1,hi);
}
int main(int argc,char**argv){
  N=atoi(argv[1]); K=atoi(argv[2]);
  FULL=(N==64)?~0ull:((1ull<<N)-1);
  for(int m=1;m<=N;m++){int r=reachv(m);L[m]=R[m]=0;for(int d=1;d<=r;d++){L[m]|=1ull<<(m-d-1);R[m]|=1ull<<(m+d-1);}}
  ht=malloc(sizeof(u64)<<HB); hmask=(1ull<<HB)-1;
  int t0=(N+2)/3;
  for(T=t0;T>=1;T--){ nset=nnotG=nunres=0; enumsets(0,T,0,N+1-T);
    printf("N=%d k=%d centrality=%d (ceil(N/3)=%d): sets=%ld notG=%ld unresolved=%ld\n",N,K,T,t0,nset,nnotG,nunres);
    if(nunres)break; }
  return 0;
}

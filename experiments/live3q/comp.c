/* comp.c N x1 x2 ... : DFS completion after the background {x1, x2, ...}; prints the order
   in which the remaining panels are placed (centre-ordered candidates, memo of failures).
   Option: env ORD=c to use candidate order by distance to c (default (N+1)/2). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
static int N; static u64 L[70], R[70], FULL;
static int reachv(int m){int a=m-1,b=N-m;return a<b?a:b;}
static int imb(u64 S,int m){return __builtin_popcountll(S&L[m])-__builtin_popcountll(S&R[m]);}
#define HB 22
static u64 *ht; static size_t hmask; static long nodes;
static int hfind(u64 s){size_t h=(s*0x9E3779B97F4A7C15ull)>>(64-HB);while(ht[h]){if(ht[h]==s)return 1;h=(h+1)&hmask;}return 0;}
static void hins(u64 s){size_t h=(s*0x9E3779B97F4A7C15ull)>>(64-HB);while(ht[h]){if(ht[h]==s)return;h=(h+1)&hmask;}ht[h]=s;}
static int ord[70], path[70], depth;
static int dfs(u64 S){
  if(S==FULL)return 1;
  if(++nodes>20000000)return 0;
  if(hfind(S))return 0;
  for(int i=0;i<N;i++){int m=ord[i]; if(S>>(m-1)&1)continue; if(imb(S,m)==0){path[depth++]=m; if(dfs(S|1ull<<(m-1)))return 1; depth--;}}
  hins(S);return 0;
}
int main(int argc,char**argv){
  N=atoi(argv[1]); FULL=(N==64)?~0ull:((1ull<<N)-1);
  for(int m=1;m<=N;m++){int r=reachv(m);L[m]=R[m]=0;for(int d=1;d<=r;d++){L[m]|=1ull<<(m-d-1);R[m]|=1ull<<(m+d-1);}}
  u64 B=0; for(int i=2;i<argc;i++)B|=1ull<<(atoi(argv[i])-1);
  double c=(N+1)/2.0; if(getenv("ORD"))c=atof(getenv("ORD"));
  for(int i=0;i<N;i++)ord[i]=i+1;
  for(int i=0;i<N;i++)for(int j=i+1;j<N;j++){double di=ord[i]-c,dj=ord[j]-c;if(di<0)di=-di;if(dj<0)dj=-dj;if(dj<di){int x=ord[i];ord[i]=ord[j];ord[j]=x;}}
  ht=calloc(1ull<<HB,sizeof(u64)); hmask=(1ull<<HB)-1;
  if(dfs(B)){for(int i=0;i<depth;i++)printf("%d ",path[i]);printf("\n");}
  else printf("FAIL nodes=%ld\n",nodes);
  return 0;}

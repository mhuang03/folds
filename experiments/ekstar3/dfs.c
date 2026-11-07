/* dfs.c N x1 x2 ... : a background ordering of [N] \ D on the background D (DFS, memo of failed
   states, candidate order by distance from a centre; tries several centres).  Prints it. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned _BitInt(256) u;
#define HB 23
static int N; static u L[260],R[260],FULL;
static int popc(u x){int s=0;for(int i=0;i<4;i++){s+=__builtin_popcountll((unsigned long long)x);x>>=64;}return s;}
static size_t hh(u s){unsigned long long a=(unsigned long long)s,b=(unsigned long long)(s>>64),c=(unsigned long long)(s>>128),d=(unsigned long long)(s>>192);return (size_t)((((a^(b*0x9E3779B97F4A7C15ull))^(c*0xC2B2AE3D27D4EB4Full))^(d*0x165667B19E3779F9ull))*0x9E3779B97F4A7C15ull)>>(64-HB);}
static u *ht; static size_t hmask; static long nodes,lim=20000000;
static int hfind(u s){size_t h=hh(s);while(ht[h]){if(ht[h]==s)return 1;h=(h+1)&hmask;}return 0;}
static void hins(u s){size_t h=hh(s);while(ht[h]){if(ht[h]==s)return;h=(h+1)&hmask;}ht[h]=s;}
static int ord[260],path[260],depth;
static int imb(u S,int m){return popc(S&L[m])-popc(S&R[m]);}
static int dfs(u S){ if(S==FULL)return 1; if(++nodes>lim)return 0; if(hfind(S))return 0;
  for(int i=0;i<N;i++){int m=ord[i]; if(S>>(m-1)&1)continue; if(imb(S,m)==0){path[depth++]=m; if(dfs(S|(u)1<<(m-1)))return 1; depth--;}}
  hins(S); return 0;}
int main(int argc,char**argv){ N=atoi(argv[1]); FULL=(((u)1<<N)-1);
  for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m;L[m]=R[m]=0;for(int d=1;d<=r;d++){L[m]|=(u)1<<(m-d-1);R[m]|=(u)1<<(m+d-1);}}
  u B=0; for(int i=2;i<argc;i++)B|=(u)1<<(atoi(argv[i])-1);
  ht=malloc(sizeof(u)<<HB); hmask=((size_t)1<<HB)-1;
  double cs[9]={(N+1)/2.0,1.0,N,(N+1)/4.0,3*(N+1)/4.0,(N+1)/3.0,2*(N+1)/3.0,(N+1)/5.0,4*(N+1)/5.0};
  for(int t=0;t<9;t++){ double c=cs[t];
    for(int i=0;i<N;i++)ord[i]=i+1;
    for(int i=0;i<N;i++)for(int j=i+1;j<N;j++){double di=ord[i]-c,dj=ord[j]-c;if(di<0)di=-di;if(dj<0)dj=-dj;if(dj<di){int x=ord[i];ord[i]=ord[j];ord[j]=x;}}
    memset(ht,0,sizeof(u)<<HB); nodes=0; depth=0;
    if(dfs(B)){ printf("OK centre %.1f:",c); for(int i=0;i<depth;i++)printf(" %d",path[i]); printf("\n"); return 0;}
  }
  printf("FAIL\n"); return 1;}

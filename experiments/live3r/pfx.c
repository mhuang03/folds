/* pfx.c N ORD x1 x2 ...: DFS completion after the background (candidates by distance to ORD),
   then the first prefix of the completion after which the background satisfies Theorem G;
   prints that prefix (the "steps") and the centre. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 W;
static int N; static W Lm[130], Rm[130], FULL;
static int pc(W x){return __builtin_popcountll((unsigned long long)x)+__builtin_popcountll((unsigned long long)(x>>64));}
static int reachn(int n,int m){int a=m-1,b=n-m;return a<b?a:b;}
static int imb(W S,int m){return pc(S&Lm[m])-pc(S&Rm[m]);}
static int centre(W B){ int maxneg=0,minpos=N+1;
  for(int m=1;m<=N;m++){ if((B>>(m-1))&1)continue; int I=imb(B,m); if(I<0&&m>maxneg)maxneg=m; if(I>0&&m<minpos)minpos=m;}
  return maxneg<minpos ? 2*maxneg+1 : -1; }
#define HB 25
static W *ht; static size_t hmask; static long nodes;
static size_t hh(W s){unsigned long long a=(unsigned long long)s,b=(unsigned long long)(s>>64);return ((a^(b*0x9E3779B97F4A7C15ull))*0x9E3779B97F4A7C15ull)>>(64-HB);}
static int hfind(W s){size_t h=hh(s);while(ht[h]){if(ht[h]==s)return 1;h=(h+1)&hmask;}return 0;}
static void hins(W s){size_t h=hh(s);while(ht[h]){if(ht[h]==s)return;h=(h+1)&hmask;}ht[h]=s;}
static int ord[130], path[130], depth; static long LIM=5000000;
/* prefer reaching an inward set: stop as soon as the background is inward */
static int dfs(W S){
  if(centre(S)>=0)return 1;
  if(++nodes>LIM)return 0;
  if(hfind(S))return 0;
  for(int i=0;i<N;i++){int m=ord[i]; if((S>>(m-1))&1)continue; if(imb(S,m)==0){path[depth++]=m; if(dfs(S|((W)1<<(m-1))))return 1; depth--;}}
  hins(S);return 0;}
int main(int argc,char**argv){
  N=atoi(argv[1]); double c=atof(argv[2]); FULL=((W)1<<N)-1; if(getenv("LIM"))LIM=atol(getenv("LIM"));
  for(int m=1;m<=N;m++){int r=reachn(N,m);Lm[m]=Rm[m]=0;for(int d=1;d<=r;d++){Lm[m]|=(W)1<<(m-d-1);Rm[m]|=(W)1<<(m+d-1);}}
  W B=0; int i=3; for(;i<argc;i++){ if(argv[i][0]=='-')break; B|=(W)1<<(atoi(argv[i])-1);}
  /* forced valid steps after "-" */
  for(i++;i<argc;i++){ int m=atoi(argv[i]); if(((B>>(m-1))&1)||imb(B,m)!=0){printf("forced step %d invalid\n",m);return 1;} B|=(W)1<<(m-1); printf("%d ",m); }
  for(int i=0;i<N;i++)ord[i]=i+1;
  for(int i=0;i<N;i++)for(int j=i+1;j<N;j++){double di=ord[i]-c,dj=ord[j]-c;if(di<0)di=-di;if(dj<0)dj=-dj;if(dj<di){int x=ord[i];ord[i]=ord[j];ord[j]=x;}}
  ht=calloc((size_t)1<<HB,sizeof(W)); hmask=((size_t)1<<HB)-1;
  if(dfs(B)){ W S=B; for(int i=0;i<depth;i++)S|=(W)1<<(path[i]-1);
    printf("%d steps:",depth); for(int i=0;i<depth;i++)printf(" %d",path[i]); printf("  c2=%d\n",centre(S)); }
  else printf("FAIL nodes=%ld\n",nodes);
  return 0;}

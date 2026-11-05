/* enumerate admissible labellings c:[1..N]->{0..t-1}:
   for all m: #{x in L(m): c x <= c m} <= #{x in R(m): c x < c m}
   usage: enum N t [print]   prints count (and labellings if print) */
#include <stdio.h>
#include <stdlib.h>
int N,T,PR; int c[200]; long long cnt=0;
static int r(int m){int a=m-1,b=N-m;return a<b?a:b;}
/* check feasibility of all assigned m given positions 1..p assigned */
static int ok(int p){
  for(int m=1;m<=p;m++){int R=r(m); if(!R) continue; int v=c[m];
    int lhs=0; for(int x=m-R;x<m;x++) if(c[x]<=v) lhs++;
    int rhs=0,un=0; for(int x=m+1;x<=m+R;x++){ if(x>p) un++; else if(c[x]<v) rhs++;}
    if(lhs>rhs+un) return 0;}
  return 1;}
static void dfs(int p){
  if(p==N){cnt++; if(PR){for(int i=1;i<=N;i++)printf("%d",c[i]);printf("\n");} return;}
  for(int v=0;v<T;v++){c[p+1]=v; if(ok(p+1)) dfs(p+1);}
}
int main(int argc,char**argv){N=atoi(argv[1]);T=atoi(argv[2]);PR=argc>3;dfs(0);fprintf(stderr,"N=%d t=%d count=%lld\n",N,T,cnt);return 0;}

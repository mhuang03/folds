// vdc.c qlo qhi : is there a GoodL(q, nu) order that is a full binary parity tree (every
// residue class mod 2^k of the q-strip is split into its two subclasses mod 2^(k+1), the
// order of the two halves chosen freely at every node)?  DFS over the choices.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int q,nu; static uint64_t Lm[70],Rm[70]; static int sg[70];
static inline int val(uint64_t S,int t){ return __builtin_popcountll(S&Lm[t])==__builtin_popcountll(S&Rm[t]); }
typedef struct { int a,d,c; } Node;
static long nodes;
static int dfs(Node *st,int sp,uint64_t S,uint64_t T){
  if(sp==0) return 1; if(++nodes>50000000L) return 0;
  Node x=st[sp-1]; sp--;
  if(x.c==1){ int t=x.a,u=sg[t]; if(!val(S,t)||!val(T,u)) return 0; return dfs(st,sp,S|1ULL<<t,T|1ULL<<u); }
  Node c1={x.a,2*x.d,(x.c+1)/2}, c2={x.a+x.d,2*x.d,x.c/2};
  Node st2[140]; for(int i=0;i<sp;i++) st2[i]=st[i];
  st2[sp]=c2; st2[sp+1]=c1; if(dfs(st2,sp+2,S,T)) return 1;
  st2[sp]=c1; st2[sp+1]=c2; if(dfs(st2,sp+2,S,T)) return 1;
  return 0; }
int main(int argc,char**argv){ int lo=atoi(argv[1]),hi=atoi(argv[2]);
  for(q=lo;q<=hi;q++){ printf("q=%d:",q);
    for(int t=1;t<=q;t++){ int r=t-1<q-t?t-1:q-t; Lm[t]=Rm[t]=0; for(int j=1;j<=r;j++){Lm[t]|=1ULL<<(t-j);Rm[t]|=1ULL<<(t+j);} }
    for(nu=0;nu<q;nu++){ for(int t=1;t<=q;t++) sg[t]=((nu-t)%q+q)%q+1; Node st[140]; st[0]=(Node){1,1,q}; nodes=0; int ok=dfs(st,1,0,0); printf("%c",ok?'Y':(nodes>50000000L?'?':'.')); }
    printf("\n"); }
}

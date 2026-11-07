// vdcrule.c q nu : parity-tree GoodL orders (see vdc.c).  For every node (class a mod d of the
// q-strip, d = 2^k) report which choices occur in some solution: L = lower class (a mod 2d)
// first, U = upper class (a + d mod 2d) first, B = both possible, - = no solution.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int q,nu; static uint64_t Lm[70],Rm[70]; static int sg[70];
static inline int val(uint64_t S,int t){ return __builtin_popcountll(S&Lm[t])==__builtin_popcountll(S&Rm[t]); }
typedef struct { int a,d,c; } Node;
static int force[70][70]; // force[d-index][a]: 0 free, 1 lower first, 2 upper first
static long nodes;
static int lg(int d){ int k=0; while((1<<k)<d) k++; return k; }
static int dfs(Node *st,int sp,uint64_t S,uint64_t T){
  if(sp==0) return 1; if(++nodes>20000000L) return 0;
  Node x=st[sp-1]; sp--;
  if(x.c==1){ int t=x.a,u=sg[t]; if(!val(S,t)||!val(T,u)) return 0; return dfs(st,sp,S|1ULL<<t,T|1ULL<<u); }
  Node c1={x.a,2*x.d,(x.c+1)/2}, c2={x.a+x.d,2*x.d,x.c/2};
  Node st2[140]; for(int i=0;i<sp;i++) st2[i]=st[i]; int f=force[lg(x.d)][x.a];
  if(f!=2){ st2[sp]=c2; st2[sp+1]=c1; if(dfs(st2,sp+2,S,T)) return 1; }
  if(f!=1){ st2[sp]=c1; st2[sp+1]=c2; if(dfs(st2,sp+2,S,T)) return 1; }
  return 0; }
static int run(){ force[0][1]=1; Node st[140]; st[0]=(Node){1,1,q}; nodes=0; return dfs(st,1,0,0); }
int main(int argc,char**argv){ q=atoi(argv[1]); nu=atoi(argv[2]);
  for(int t=1;t<=q;t++){ int r=t-1<q-t?t-1:q-t; Lm[t]=Rm[t]=0; for(int j=1;j<=r;j++){Lm[t]|=1ULL<<(t-j);Rm[t]|=1ULL<<(t+j);} sg[t]=((nu-t)%q+q)%q+1; }
  printf("q=%d nu=%d exists=%d\n",q,nu,run());
  for(int d=1;d<q;d*=2){ printf("d=%2d:",d); for(int a=1;a<=d&&a<=q;a++){ int c=(q-a)/d+1; if(c<2){ printf(" %d:.",a); continue; }
      force[lg(d)][a]=1; int l=run(); force[lg(d)][a]=2; int u=run(); force[lg(d)][a]=0;
      printf(" %d:%c",a,l&&u?'B':l?'L':u?'U':'-'); } printf("\n"); }
}

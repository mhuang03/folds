// Fully valid sets: X subset [N] such that every panel outside X is a valid move after X.
// For each, report |X|, g(X) (valid orderings from scratch in the N-strip).
// By the general slip lemma (zero defect) the completions of X contain all a(N-|X|)
// strip-valid orders of the complement, so a(N) >= sum_X g(X) a(N-|X|)... (per size).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int N; static const double AV[]={1,1,2,4,10,28,96,256,1120,4256,17878,70960,383476,1620328,9167908,47821296,276182312,1481994716,10084180418.,55082188120.,398874108930.,2505681033958.,18168130281086.,119006527671252.,979730153850974.,6564449510287388.};
static int valid(unsigned S,int m){ int r = m-1 < N-m ? m-1 : N-m; int l=0,rr=0;
  for(int d=1; d<=r; d++){ l += (S>>(m-1-d))&1; rr += (S>>(m-1+d))&1; } return l==rr; }
int main(int argc,char**argv){ N=atoi(argv[1]); unsigned full=(1u<<N)-1;
  double *g=calloc(1u<<N,sizeof(double)); g[0]=1;
  for(unsigned S=1;S<=full;S++){ double s=0; for(int m=1;m<=N;m++) if((S>>(m-1))&1){ unsigned T=S&~(1u<<(m-1)); if(g[T]>0 && valid(T,m)) s+=g[T]; } g[S]=s; }
  // a(k) for k<=N: need a of smaller strips; read from argv? compute quickly via recursion is heavy; print g only
  for(unsigned S=0;S<full;S++){ if(g[S]==0) continue; int ok=1; for(int m=1;m<=N&&ok;m++) if(!((S>>(m-1))&1) && !valid(S,m)) ok=0;
    if(ok){ printf("ratio=%.4f k=%2d g=%12.0f X=",g[S]/AV[__builtin_popcount(S)],__builtin_popcount(S),g[S]); for(int m=1;m<=N;m++) putchar((S>>(m-1))&1?'x':'.'); putchar('\n'); } }
  printf("a(N)=%.0f\n",g[full]);
}

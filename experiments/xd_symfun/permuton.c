/* Average permutation matrix of V_N:  C[k][m] = #{a in V_N : a_k = m}, by the subset DP
     C[k][m] = sum_{|S| = k-1, m not in S, step (S,m) valid} g(S) g([N] \ S \ {m})
   (g(S) = number of valid orderings of S; completions of S u {m} are counted by g of the
   complement, by reversal).  usage: permuton N   -> N lines of N integers (row k = step). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef uint64_t u64;
int main(int argc,char**argv){
  int N=atoi(argv[1]); u64 full=(1ULL<<N)-1, L[64],R[64];
  for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m;L[m]=R[m]=0;
    for(int d=1;d<=r;d++){L[m]|=1ULL<<(m-d-1);R[m]|=1ULL<<(m+d-1);}}
  u64 *g=calloc(full+1,8); if(!g){fprintf(stderr,"oom\n");return 1;}
  g[0]=1;
  for(u64 S=0;S<full;S++){ if(!g[S])continue;
    for(int m=1;m<=N;m++){u64 b=1ULL<<(m-1); if(S&b)continue;
      if(__builtin_popcountll(S&L[m])!=__builtin_popcountll(S&R[m]))continue;
      g[S|b]+=g[S]; } }
  static u64 C[64][64];
  for(u64 S=0;S<full;S++){ if(!g[S])continue; int k=__builtin_popcountll(S);
    for(int m=1;m<=N;m++){u64 b=1ULL<<(m-1); if(S&b)continue;
      if(__builtin_popcountll(S&L[m])!=__builtin_popcountll(S&R[m]))continue;
      C[k][m-1]+=g[S]*g[full^S^b]; } }
  for(int k=0;k<N;k++){ for(int m=0;m<N;m++) printf("%llu ",(unsigned long long)C[k][m]); printf("\n"); }
  fprintf(stderr,"N=%d a(N)=%llu\n",N,(unsigned long long)g[full]);
  return 0; }

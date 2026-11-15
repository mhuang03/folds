/* kdp.c N [mode]
 * Subset DP (2^N states, u64 arithmetic mod 2^64; exact while the true value < 2^64,
 * i.e. N <= 28 for a(N) and everything below it).
 *  mode a : a(N)   g(S) = sum_{m valid} g(S-m)
 *  mode k : K(N)   number of swap classes (valid traces) by Cartier-Foata inclusion-exclusion
 *                  on the set of maximal pieces:
 *                  K(S) = sum_{m valid} K(S-m) - sum_{{m,m'} independent, both valid wrt S-m-m'} K(S-m-m')
 *  mode s : signed count  sum_{a valid} sgn(a)   (sgn = (-1)^inversions of the sequence)
 *  mode t : AO(N)  number of ALL traces with each panel once (no validity) = number of
 *                  acyclic orientations of the dependence graph (same recursion, no validity test)
 *  mode f : F(N)   number of valid sequences in "parallel form": sequences of blocks, each a
 *                  single panel or an independent pair, with NO sign (= sum_a 2^{up(a)})
 * Prints the value and the number of nonzero states.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef uint64_t u64;
int main(int argc,char**argv){
  int N=atoi(argv[1]); char mode=argc>2?argv[2][0]:'k';
  u64 full=(1ULL<<N)-1;
  u64 *c=calloc(1ULL<<N,sizeof(u64));
  if(!c){fprintf(stderr,"alloc\n");return 1;}
  u64 Lm[64],Rm[64],W[64],indm[64];
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m; Lm[m]=0;Rm[m]=0;
    for(int d=1;d<=D;d++){Lm[m]|=1ULL<<(m-d-1);Rm[m]|=1ULL<<(m+d-1);} W[m]=Lm[m]|Rm[m]; }
  for(int m=1;m<=N;m++){ indm[m]=0; for(int x=m+1;x<=N;x++) if(!((W[m]>>(x-1))&1) && !((W[x]>>(m-1))&1)) indm[m]|=1ULL<<(x-1); }
  c[0]=1; u64 nz=0;
  for(u64 S=0;S<=full;S++){ u64 v=c[S]; if(!v){ continue; } nz++; if(S==full) break;
    u64 ok=0;
    for(int m=1;m<=N;m++){ u64 b=1ULL<<(m-1); if(S&b)continue;
      if(mode=='t' || __builtin_popcountll(S&Lm[m])==__builtin_popcountll(S&Rm[m])) ok|=b; }
    for(u64 t=ok;t;t&=t-1){ int m=__builtin_ctzll(t)+1; u64 b=1ULL<<(m-1);
      if(mode=='s'){ if(__builtin_popcountll(S>>m)&1) c[S|b]-=v; else c[S|b]+=v; }
      else c[S|b]+=v;
      if(mode=='k'||mode=='t'||mode=='f'){
        for(u64 u=ok&indm[m];u;u&=u-1){ u64 b2=u&-u; if(mode=='f') c[S|b|b2]+=v; else c[S|b|b2]-=v; }
      }
    }
  }
  printf("N=%d mode=%c value=%lld (unsigned %llu) nonzero_states=%llu\n",N,mode,(long long)c[full],(unsigned long long)c[full],(unsigned long long)nz);
  return 0;
}

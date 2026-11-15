/* zdp.c N
 * Z(N) = number of RIGID valid sequences (no two adjacent steps independent), and
 * D1(N) = number of valid sequences with exactly ... (not computed here).
 * DP over (S, last): z[S][last] = number of valid orderings of S ending in `last` with every
 * adjacent pair dependent.  Memory 2^N * N * 8 bytes  (N <= 22: 0.74 GB).
 * Also prints Zset(N) = number of sets S that are the prefix set of some rigid ordering.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef uint64_t u64;
int main(int argc,char**argv){
  int N=atoi(argv[1]);
  u64 full=(1ULL<<N)-1;
  u64 *z=calloc((size_t)N<<N,sizeof(u64));
  if(!z){fprintf(stderr,"alloc\n");return 1;}
  u64 Lm[64],Rm[64],W[64],dep[64];
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m; Lm[m]=0;Rm[m]=0;
    for(int d=1;d<=D;d++){Lm[m]|=1ULL<<(m-d-1);Rm[m]|=1ULL<<(m+d-1);} W[m]=Lm[m]|Rm[m]; }
  for(int m=1;m<=N;m++){ dep[m]=0; for(int x=1;x<=N;x++) if(x!=m && (((W[m]>>(x-1))&1) || ((W[x]>>(m-1))&1))) dep[m]|=1ULL<<(x-1); }
  for(int m=1;m<=N;m++) z[((u64)1<<(m-1))*N+(m-1)]=1;
  u64 nsets=0; u64 maxk_sets[64]={0};
  for(u64 S=1;S<=full;S++){
    u64 *row=z+S*N; int any=0;
    for(int l=0;l<N;l++) if(row[l]) any=1;
    if(!any) continue;
    nsets++; maxk_sets[__builtin_popcountll(S)]++;
    if(S==full) break;
    for(int m=1;m<=N;m++){ u64 b=1ULL<<(m-1); if(S&b)continue;
      if(__builtin_popcountll(S&Lm[m])!=__builtin_popcountll(S&Rm[m])) continue;
      u64 s=0; for(u64 t=dep[m]&S;t;t&=t-1){ s+=row[__builtin_ctzll(t)]; }
      if(s) z[(S|b)*N+(m-1)]+=s; }
  }
  u64 Z=0; for(int l=0;l<N;l++) Z+=z[full*N+l];
  printf("N=%d Z=%llu rigid_prefix_sets=%llu  by size:",N,(unsigned long long)Z,(unsigned long long)nsets);
  for(int k=1;k<=N;k++) printf(" %llu",(unsigned long long)maxk_sets[k]);
  printf("\n");
  return 0;
}

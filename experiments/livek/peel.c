/* peel.c: Theorem G versus Theorem G' (sign schemes, decided by peeling; adjacent/PROOFS.txt 2)
   on all k-subsets of [N], by centrality t = min(min D, N+1-max D).
   Peeling: repeatedly remove a free panel m with (I_D(m) <= 0 and no remaining panel in L(m))
   or (I_D(m) >= 0 and no remaining panel in R(m)); G' holds iff everything is removed.
   Usage: peel N k     Output: per t: sets, not G, not G'. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef uint64_t u64;
static int N, K; static u64 L[70], R[70];
static int reachv(int m){int a=m-1,b=N-m;return a<b?a:b;}
static int imb(u64 S,int m){return __builtin_popcountll(S&L[m])-__builtin_popcountll(S&R[m]);}
static int inwardG(u64 B){ int maxneg=0,minpos=N+1;
  for(int m=1;m<=N;m++){ if(B>>(m-1)&1)continue; int I=imb(B,m); if(I<0&&m>maxneg)maxneg=m; if(I>0&&m<minpos)minpos=m;}
  return maxneg<minpos; }
static int peel(u64 B){ u64 rem=0; int I[70];
  for(int m=1;m<=N;m++) if(!(B>>(m-1)&1)){rem|=1ull<<(m-1); I[m]=imb(B,m);}
  int prog=1; while(rem&&prog){prog=0; for(int m=1;m<=N;m++){ if(!(rem>>(m-1)&1))continue;
      if((I[m]<=0&&!(rem&L[m]))||(I[m]>=0&&!(rem&R[m]))){rem&=~(1ull<<(m-1));prog=1;}}}
  return rem==0; }
static long cnt[70][3];
static void enumsets(u64 S,int start,int depth){
  if(depth==K){ int mn=__builtin_ctzll(S)+1, mx=64-__builtin_clzll(S); int c=mn<N+1-mx?mn:N+1-mx;
    cnt[c][0]++; if(!inwardG(S))cnt[c][1]++; if(!peel(S))cnt[c][2]++; return;}
  for(int m=start;m<=N;m++)enumsets(S|1ull<<(m-1),m+1,depth+1);
}
int main(int argc,char**argv){
  N=atoi(argv[1]); K=atoi(argv[2]);
  for(int m=1;m<=N;m++){int r=reachv(m);L[m]=R[m]=0;for(int d=1;d<=r;d++){L[m]|=1ull<<(m-d-1);R[m]|=1ull<<(m+d-1);}}
  enumsets(0,1,0);
  printf("N=%d k=%d (t: sets/notG/notG')",N,K);
  for(int t=1;2*t<=N+1;t++) if(cnt[t][0]) printf(" %d:%ld/%ld/%ld",t,cnt[t][0],cnt[t][1],cnt[t][2]);
  printf("\n"); return 0;
}

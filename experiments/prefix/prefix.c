/* prefix.c: T(N,k) = number of length-k sequences of distinct panels in [1..N]
 * in which every step is semi-symmetric (valid).
 * usage: prefix K Nmin Nmax [brute]
 * DFS over prefixes of length K-1; the last level is counted by a breakpoint sweep
 * (f(m) = L(m)-R(m) is piecewise constant in m between O(|S|) breakpoints).
 * Mirror symmetry m -> N+1-m halves the work at the first level.
 * Output: N T(N,1) ... T(N,K). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long u64;
static int N, K, S[16], ns, inS[1024];
static u64 cnt[16];
static int brute = 0;

static int f(int m){ /* L - R for m not in S */
  int L=0,R=0;
  if (m-1 <= N-m){ int hi=2*m-1;
    for(int i=0;i<ns;i++){int x=S[i]; if(x<m) L++; else if(x<=hi) R++;} }
  else { int lo=2*m-N;
    for(int i=0;i<ns;i++){int x=S[i]; if(x>m) R++; else if(x>=lo) L++;} }
  return L-R;
}
static int cmpi(const void*a,const void*b){return *(int*)a-*(int*)b;}
static u64 count_last(void){
  if (brute){ u64 c=0; for(int m=1;m<=N;m++) if(!inS[m] && f(m)==0) c++; return c; }
  int b[128], nb=0;
  int m0=(N+1)/2; /* m<=m0 is left half (m-1<=N-m) */
  b[nb++]=1; b[nb++]=N+1; b[nb++]=m0+1;
  for(int i=0;i<ns;i++){int x=S[i];
    b[nb++]=x; b[nb++]=x+1; b[nb++]=(x+2)/2; b[nb++]=(x+N)/2+1; }
  qsort(b,nb,sizeof(int),cmpi);
  u64 c=0;
  for(int i=0;i<nb-1;i++){ int lo=b[i], hi=b[i+1]; if(lo==hi||lo<1||hi>N+1) continue;
    if(inS[lo]) continue; /* segment {x} */
    if(f(lo)==0) c += hi-lo; }
  return c;
}
static void dfs(int depth, u64 w){ /* depth = ns */
  if (depth==K-1){ cnt[K] += w*count_last(); return; }
  for(int m=1;m<=N;m++){ if(inS[m]) continue; if(f(m)!=0) continue;
    cnt[depth+1]+=w;
    S[ns++]=m; inS[m]=1; dfs(depth+1,w); ns--; inS[m]=0; }
}
int main(int argc,char**argv){
  K=atoi(argv[1]); int a=atoi(argv[2]), bN=atoi(argv[3]); brute=argc>4;
  for(N=a;N<=bN;N++){
    memset(cnt,0,sizeof cnt); memset(inS,0,sizeof inS); ns=0;
    if (K==1){ printf("%d %d\n",N,N); continue; }
    for(int m=1;m<=(N+1)/2;m++){ u64 w = (2*m==N+1)?1:2;
      cnt[1]+=w; S[ns++]=m; inS[m]=1; dfs(1,w); ns--; inS[m]=0; }
    printf("%d",N); for(int k=1;k<=K;k++) printf(" %llu",cnt[k]); printf("\n"); fflush(stdout);
  }
}

/* classes.c N [dump]
 * Enumerate all valid (semi-symmetric) sequences of [N] and analyse the swap classes
 * (= traces for the fixed independence relation I: x,y independent iff x not in W(y) and
 * y not in W(x)).
 *
 * For each valid sequence a:
 *   up(a)   = #{p : a_p, a_{p+1} independent, a_p < a_{p+1}}
 *   down(a) = #{p : a_p, a_{p+1} independent, a_p > a_{p+1}}
 *   a is the TOP of its class iff up = 0 (max number of inversions), BOTTOM iff down = 0,
 *   RIGID iff up = down = 0.
 * For each top: the class is the set of shuffles of its left-half subsequence l_1..l_A and
 * right-half subsequence r_1..r_B that orient every dependent cross pair as in a.  With
 * lo_p <= (number of r placed before l_p) <= hi_p this is a count of lattice paths, done by
 * DP; we also get the signed count sum (-1)^{rank}, and the length (rank of the top).
 * Output: K(N) (#classes), Z(N), histogram of valid-swap degree, class size histogram,
 * largest class, sum of sizes (must equal a(N)), sum over classes of |signed count|, ...
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned long long u64;
static int N, H;               /* H = N/2: panels 1..H are "left", H+1..N "right" */
static int ind[40][40];
static u64 Lm[40], Rm[40];
static int a[40];
static u64 cntAll, cntTop, cntBot, cntRigid;
static u64 degHist[40], upHist[40];
static u64 *sizes; static size_t nsz, capsz;
static long long *signedc;     /* signed counts per class */
static int *lens;
static u64 maxSize; static int maxSeq[40];
static int dumpFlag;
static int inwin(int m, int x){ int r = m-1 < N-m ? m-1 : N-m; int d = x>m ? x-m : m-x; return x!=m && d<=r; }

static void analyseTop(void){
  int l[40], r[40], posl[40], posr[40], A=0, B=0;
  for(int p=0;p<N;p++){ if(a[p]<=H){ l[A]=a[p]; posl[A]=p; A++; } else { r[B]=a[p]; posr[B]=p; B++; } }
  int lo[40], hi[40];
  for(int p=0;p<A;p++){
    lo[p]=0; hi[p]=B;
    for(int q=0;q<B;q++) if(!ind[l[p]][r[q]]){
      if(posr[q]<posl[p]){ if(q+1>lo[p]) lo[p]=q+1; }
      else { if(q<hi[p]) hi[p]=q; }
    }
  }
  /* DP: f[p][q] = #ways with p lefts and q rights placed; sgn version too */
  static u64 f[41][41]; static long long s[41][41];
  for(int p=0;p<=A;p++) for(int q=0;q<=B;q++){ f[p][q]=0; s[p][q]=0; }
  f[0][0]=1; s[0][0]=1;
  for(int p=0;p<=A;p++) for(int q=0;q<=B;q++){
    if(p==0&&q==0) continue;
    u64 v=0; long long w=0;
    if(q>0){ v+=f[p][q-1]; w+=s[p][q-1]; }
    if(p>0 && lo[p-1]<=q && q<=hi[p-1]){ v+=f[p-1][q]; w+= (q&1)? -s[p-1][q] : s[p-1][q]; }
    f[p][q]=v; s[p][q]=w;
  }
  u64 sz=f[A][B]; long long sg=s[A][B];
  /* effective bounds -> length of the interval */
  int elo[40], ehi[40];
  for(int p=0;p<A;p++){ elo[p]=lo[p]; if(p>0&&elo[p-1]>elo[p]) elo[p]=elo[p-1]; }
  for(int p=A-1;p>=0;p--){ ehi[p]=hi[p]; if(p<A-1&&ehi[p+1]<ehi[p]) ehi[p]=ehi[p+1]; }
  int len=0; for(int p=0;p<A;p++) len+=ehi[p]-elo[p];
  if(nsz==capsz){ capsz=capsz?2*capsz:1024; sizes=realloc(sizes,capsz*sizeof(u64));
    signedc=realloc(signedc,capsz*sizeof(long long)); lens=realloc(lens,capsz*sizeof(int)); }
  sizes[nsz]=sz; signedc[nsz]=sg<0?-sg:sg; lens[nsz]=len; nsz++;
  if(sz>maxSize){ maxSize=sz; memcpy(maxSeq,a,sizeof(int)*N); }
  if(dumpFlag){ printf("TOP "); for(int p=0;p<N;p++) printf("%d ",a[p]); printf(" size=%llu len=%d signed=%lld\n",sz,len,sg); }
}

static void leaf(void){
  cntAll++;
  int up=0, dn=0;
  for(int p=0;p+1<N;p++) if(ind[a[p]][a[p+1]]){ if(a[p]<a[p+1]) up++; else dn++; }
  degHist[up+dn]++; upHist[up]++;
  if(up==0){ cntTop++; analyseTop(); }
  if(dn==0) cntBot++;
  if(up==0&&dn==0){ cntRigid++; if(dumpFlag||cntRigid<=5){ printf("RIGID "); for(int p=0;p<N;p++) printf("%d ",a[p]); printf("\n"); } }
}
static void rec(int k, u64 S){
  if(k==N){ leaf(); return; }
  for(int m=1;m<=N;m++){ u64 b=1ULL<<(m-1); if(S&b) continue;
    if(__builtin_popcountll(S&Lm[m])!=__builtin_popcountll(S&Rm[m])) continue;
    a[k]=m; rec(k+1,S|b); }
}
static int cmpu(const void*x,const void*y){ u64 a_=*(const u64*)x,b_=*(const u64*)y; return a_<b_?-1:a_>b_; }
static int cmpl(const void*x,const void*y){ long long a_=*(const long long*)x,b_=*(const long long*)y; return a_<b_?-1:a_>b_; }
int main(int argc,char**argv){
  N=atoi(argv[1]); dumpFlag=argc>2; H=N/2;
  for(int m=1;m<=N;m++){ int D=m-1<N-m?m-1:N-m; Lm[m]=Rm[m]=0;
    for(int d=1;d<=D;d++){ Lm[m]|=1ULL<<(m-d-1); Rm[m]|=1ULL<<(m+d-1); } }
  int nind=0;
  for(int x=1;x<=N;x++) for(int y=1;y<=N;y++){ ind[x][y]= x!=y && !inwin(x,y) && !inwin(y,x); if(x<y&&ind[x][y]) nind++; }
  rec(0,0);
  printf("N=%d a=%llu K=%llu bottoms=%llu Z=%llu indep_pairs=%d\n",N,cntAll,cntTop,cntBot,cntRigid,nind);
  printf(" degree histogram (number of valid swaps): "); for(int d=0;d<N;d++) if(degHist[d]) printf("%d:%llu ",d,degHist[d]); printf("\n");
  printf(" up histogram: "); for(int d=0;d<N;d++) if(upHist[d]) printf("%d:%llu ",d,upHist[d]); printf("\n");
  u64 tot=0; for(size_t i=0;i<nsz;i++) tot+=sizes[i];
  /* length histogram, signed stats before sorting sizes */
  u64 lenHist[400]; memset(lenHist,0,sizeof lenHist); for(size_t i=0;i<nsz;i++) lenHist[lens[i]]++;
  printf(" class length (rank of top) histogram: "); for(int d=0;d<400;d++) if(lenHist[d]) printf("%d:%llu ",d,lenHist[d]); printf("\n");
  long long sumAbs=0; u64 oddCls=0; for(size_t i=0;i<nsz;i++){ sumAbs+=signedc[i]; if(sizes[i]&1) oddCls++; }
  qsort(signedc,nsz,sizeof(long long),cmpl);
  printf(" |E-O| per class histogram: "); { size_t i=0; int shown=0; while(i<nsz){ size_t j=i; while(j<nsz&&signedc[j]==signedc[i]) j++; if(shown<40) printf("%lld:%zu ",signedc[i],j-i); shown++; i=j; } printf(" (distinct %d)\n",shown); }
  printf(" sum of class sizes=%llu (%s) sum|E-O|=%lld odd-size classes=%llu\n",tot,tot==cntAll?"ok":"MISMATCH",sumAbs,oddCls);
  qsort(sizes,nsz,sizeof(u64),cmpu);
  printf(" class size histogram (size:count): "); { size_t i=0; int shown=0; while(i<nsz){ size_t j=i; while(j<nsz&&sizes[j]==sizes[i]) j++; if(shown<60) printf("%llu:%zu ",sizes[i],j-i); shown++; i=j; } printf(" (distinct sizes %d)\n",shown); }
  printf(" median class size=%llu mean=%.3f max=%llu at top ",nsz?sizes[nsz/2]:0,(double)tot/nsz,maxSize); for(int p=0;p<N;p++) printf("%d ",maxSeq[p]); printf("\n");
  return 0;
}

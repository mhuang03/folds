// minimax.c : discrepancy along valid fold sequences.
//   ./minimax N [dist]
// D(S) = max_{0<=t<=N} |N P(t) - |S| t|   (N times the star discrepancy of S at integer points).
// For a sequence a, M(a) = max over its prefix sets of D.
//   Bv = min of M over valid (semi-symmetric) sequences, and the number attaining it;
//   Bs = the same over symmetric (3-AP-free) sequences;
//   Bu = min of M over all N! permutations;
//   Mc = M of the canonical sequence (truncated bit reversal), and of every member of the
//        parity-block tree family (min and max over the 2^(N-1) members);
//   with "dist": the full distribution #{valid a : M(a) <= theta} for every theta.
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint32_t u32; typedef unsigned long long u64;
int N; u32 Lm[40], Rm[40], full;
static inline int pc(u32 x){return __builtin_popcount(x);}
unsigned short *D;
static int validstep(u32 S0,int m){return pc(S0&Lm[m])==pc(S0&Rm[m]);}
static int symstep(u32 S0,int m){int r=(m-1<N-m)?m-1:N-m; for(int d=1;d<=r;d++){ if(((S0>>(m-d-1))&1)!=((S0>>(m+d-1))&1))return 0;} return 1;}
// tree family: enumerate all members recursively as lists
static int best_tree_min, best_tree_max; static long long ntree;
static int seq[64];
static int Mof(int*a){u32 S=0;int M=0;for(int i=0;i<N;i++){S|=1u<<(a[i]-1); if(D[S]>M)M=D[S];} return M;}
// build all tree-family sequences of the class {off + step*y : y=1..n}; returns list of lists (exponential) -- only for small N
typedef struct {int n; int cnt; int *data;} LL;
static LL build(int n){ LL r; r.n=n; if(n<=1){r.cnt=1; r.data=malloc(sizeof(int)*(n>0?n:1)); if(n==1)r.data[0]=1; return r;}
  LL o=build((n+1)/2), e=build(n/2); r.cnt=2*o.cnt*e.cnt; r.data=malloc(sizeof(int)*(size_t)r.cnt*n); int c=0;
  for(int i=0;i<o.cnt;i++)for(int j=0;j<e.cnt;j++){
    int*p=r.data+(size_t)c*n; for(int x=0;x<o.n;x++)p[x]=2*o.data[(size_t)i*o.n+x]-1; for(int x=0;x<e.n;x++)p[o.n+x]=2*e.data[(size_t)j*e.n+x]; c++;
    p=r.data+(size_t)c*n; for(int x=0;x<e.n;x++)p[x]=2*e.data[(size_t)j*e.n+x]; for(int x=0;x<o.n;x++)p[e.n+x]=2*o.data[(size_t)i*o.n+x]-1; c++; }
  free(o.data); free(e.data); return r; }
static void canon(int n,int off,int step,int*out,int*len){ if(n==0)return; if(n==1){out[(*len)++]=off+step;return;}
  canon((n+1)/2,off-step,2*step,out,len); canon(n/2,off,2*step,out,len);} // odds: off+step*(2y-1)=(off-step)+2step*y
int main(int argc,char**argv){
  N=atoi(argv[1]); int dist=(argc>2); full=(1u<<N)-1;
  for(int m=1;m<=N;m++){int r=(m-1<N-m)?m-1:N-m; Lm[m]=0;Rm[m]=0;
    for(int d=1;d<=r;d++){Lm[m]|=1u<<(m-d-1);Rm[m]|=1u<<(m+d-1);} }
  size_t tot=(size_t)1<<N; D=malloc(tot*sizeof(unsigned short));
  for(u32 S=0;;S++){int s=pc(S),P=0,me=0; for(int t=1;t<=N;t++){P+=(S>>(t-1))&1; int e=N*P-s*t; if(e<0)e=-e; if(e>me)me=e;} D[S]=me; if(S==full)break;}
  unsigned short *Bv=malloc(tot*2),*Bu=malloc(tot*2),*Bs=malloc(tot*2); const unsigned short INF=65535;
  Bv[0]=Bu[0]=Bs[0]=0;
  for(u32 S=1;;S++){ unsigned short bv=INF,bu=INF,bs=INF; u32 T=S;
    while(T){int i=__builtin_ctz(T);T&=T-1; u32 S0=S&~(1u<<i); int m=i+1;
      if(Bu[S0]<bu)bu=Bu[S0];
      if(Bv[S0]<bv&&validstep(S0,m))bv=Bv[S0];
      if(Bs[S0]<bs&&symstep(S0,m))bs=Bs[S0]; }
    Bu[S]=(bu>D[S])?bu:D[S]; Bv[S]=(bv==INF)?INF:((bv>D[S])?bv:D[S]); Bs[S]=(bs==INF)?INF:((bs>D[S])?bs:D[S]);
    if(S==full)break; }
  int bv=Bv[full],bu=Bu[full],bs=Bs[full];
  int c[64],len=0; canon(N,0,1,c,&len); int Mc=Mof(c);
  // count valid / symmetric / all sequences with M <= theta
  u64 *g=malloc(tot*sizeof(u64));
  #define COUNT(theta,test,res) { g[0]=1; for(u32 S=1;;S++){ u64 acc=0; if(D[S]<=(theta)){ u32 T=S; while(T){int i=__builtin_ctz(T);T&=T-1; u32 S0=S&~(1u<<i); int m=i+1; (void)m; if(g[S0]&&(test))acc+=g[S0];} } g[S]=acc; if(S==full)break;} res=g[full]; }
  u64 nv,ns,nu,ncv; COUNT(bv,validstep(S0,m),nv); COUNT(bs,symstep(S0,m),ns); COUNT(bu,1,nu); COUNT(bu,validstep(S0,m),ncv);
  printf("N=%d  Bu=%d (#perms %llu, #valid with M<=Bu: %llu)  Bv=%d (#valid attaining %llu)  Bs=%d (#sym attaining %llu)  canon M=%d",N,bu,nu,ncv,bv,nv,bs,ns,Mc);
  if(N<=20){ LL t=build(N); int mn=1<<30,mx=0; long long nmin=0; for(int i=0;i<t.cnt;i++){int M=Mof(t.data+(size_t)i*N); if(M<mn){mn=M;nmin=0;} if(M==mn)nmin++; if(M>mx)mx=M;}
    printf("  tree family: min %d (%lld of %d) max %d",mn,nmin,t.cnt,mx); free(t.data);}
  printf("\n");
  if(dist){ char*seen=calloc(65536,1); for(u32 S=0;;S++){seen[D[S]]=1; if(S==full)break;}
    u64 prev=0,total=0; double mean=0; COUNT(65535,validstep(S0,m),total);
    printf("# theta  #valid(M<=theta)  #valid(M==theta)   (theta/N)\n");
    for(int th=bv;th<=N*N/4+N;th++){ if(!seen[th])continue; u64 r; COUNT(th,validstep(S0,m),r); if(r!=prev){printf("%d %llu %llu %.4f\n",th,r,r-prev,(double)th/N); mean+=(double)(r-prev)*th;} prev=r; if(r==total)break; }
    printf("# total %llu mean M = %.4f  mean M/N = %.4f\n",total,mean/total,mean/total/N);
    // the same mean over all N! permutations (exact while N! < 2^64, i.e. N <= 20)
    if(N<=20){ u64 tp; COUNT(65535,1,tp); long double mp=0; u64 pv=0; for(int th=0;th<=N*N/4+N;th++){ if(!seen[th])continue; u64 r; COUNT(th,1,r); mp+=(long double)(r-pv)*th; pv=r; if(r==tp)break; }
      printf("# all permutations: total %llu mean M = %.4f  mean M/N = %.4f\n",tp,(double)(mp/tp),(double)(mp/tp/N)); } }
  return 0; }

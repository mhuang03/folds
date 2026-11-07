/* livek.c: valid k-prefixes of the N-strip and sufficient conditions for liveness.
   For every set B of a valid k-prefix:
     G   : the criterion of Theorem G (negative panels all left of positive panels);
     A   : compact ("central") condition  b <= 2a+1  and  2b <= N+a+2  (a = min B, b = max B);
     M   : B inside the middle window [ceil(N/3), N+1-ceil(N/3)]  (implies A);
     Y   : dyadic: 2 max B <= N+1 and y >= 2x for all x < y in B, or the mirror image;
     Z   : lagged doubling: 2 max B <= N+1 and d_{2i+1} + 2 >= 2 d_{i+1}, or the mirror;
     S   : the count form of Z proven in Lean (coReach_sparse), checked to be equivalent to Z;
     W   : general dyadic (coReach_dyadic): 2x <= y for x < y, 2 d_k <= N + d_{k-1} + 2, or mirror;
     U   : A or S or W (the explicit families of Folds/LiveK.lean);
     V   : A or E (everything proven explicit in Folds/LiveK.lean, CovK);
     E   : explicit anchored condition (coReach_anchored), see expl();
     H   : Theorem G with the centre at min B (I >= 0 at all free m > min B) or at max B;
     live: completion found (G, or DFS witness from the background B), else "unresolved".
   Also checks A => G, Y => G, Z => G on ALL k-subsets (valid or not).
   Usage: livek N k [verbose [nodfs]]   (nodfs: criteria only, no completion search)
   Output: one summary line (prefix and set counts). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
static int N, K; static u64 L[70], R[70], FULL;
static int reachv(int m){int a=m-1,b=N-m;return a<b?a:b;}
static int imb(u64 S,int m){return __builtin_popcountll(S&L[m])-__builtin_popcountll(S&R[m]);}
#define HB 22
static u64 *ht; static size_t hmask; static long nodes, limit;
static int hfind(u64 s){size_t h=(s*0x9E3779B97F4A7C15ull)>>(64-HB);while(ht[h]){if(ht[h]==s)return 1;h=(h+1)&hmask;}return 0;}
static void hins(u64 s){size_t h=(s*0x9E3779B97F4A7C15ull)>>(64-HB);while(ht[h]){if(ht[h]==s)return;h=(h+1)&hmask;}ht[h]=s;}
static int ord[70];
static int dfs(u64 S){
  if(S==FULL)return 1;
  if(++nodes>limit)return 0;
  if(hfind(S))return 0;
  for(int i=0;i<N;i++){int m=ord[i]; if(S>>(m-1)&1)continue; if(imb(S,m)==0&&dfs(S|1ull<<(m-1)))return 1;}
  hins(S);return 0;
}
static int witness(u64 B){
  for(int t=0;t<5;t++){
    double c = (t==0)? (N+1)/2.0 : (t==1? 1.0 : (t==2? N : (t==3? (N+1)/4.0 : 3*(N+1)/4.0)));
    for(int i=0;i<N;i++)ord[i]=i+1;
    for(int i=0;i<N;i++)for(int j=i+1;j<N;j++){double di=ord[i]-c,dj=ord[j]-c;if(di<0)di=-di;if(dj<0)dj=-dj;if(dj<di){int x=ord[i];ord[i]=ord[j];ord[j]=x;}}
    memset(ht,0,sizeof(u64)<<HB); nodes=0; limit=300000;
    if(dfs(B))return 1;
  }
  return 0;
}
int inwardG(u64 B){ int maxneg=0,minpos=N+1;
  for(int m=1;m<=N;m++){ if(B>>(m-1)&1)continue; int I=imb(B,m); if(I<0&&m>maxneg)maxneg=m; if(I>0&&m<minpos)minpos=m;}
  return maxneg<minpos; }
static int gk(u64 S,int k){ if(inwardG(S))return 1; if(!k)return 0; for(int m=1;m<=N;m++){ if(S>>(m-1)&1)continue; if(imb(S,m)==0&&gk(S|1ull<<(m-1),k-1))return 1;} return 0;}
static int elems(u64 B,int*d){int n=0;for(int m=1;m<=N;m++)if(B>>(m-1)&1)d[n++]=m;return n;}
static u64 mirror(u64 B){u64 M=0;for(int m=1;m<=N;m++)if(B>>(m-1)&1)M|=1ull<<(N-m);return M;}
int condA(u64 B){int d[70];int n=elems(B,d);int a=d[0],b=d[n-1];return b<=2*a+1 && 2*b<=N+a+2;}
int condM(u64 B){int d[70];int n=elems(B,d);int a0=(N+2)/3;return d[0]>=a0 && d[n-1]<=N+1-a0;}
static int dyl(u64 B){int d[70];int n=elems(B,d);if(2*d[n-1]>N+1)return 0;for(int i=0;i+1<n;i++)if(d[i+1]<2*d[i])return 0;return 1;}
int condY(u64 B){return dyl(B)||dyl(mirror(B));}
static int lagl(u64 B){int d[70];int n=elems(B,d);if(2*d[n-1]>N+1)return 0;
  /* 1-based: d_{2i+1}+2 >= 2 d_{i+1}, i>=1, 2i+1<=n  ->  0-based d[2i]+2 >= 2 d[i] */
  for(int i=1;2*i<n;i++)if(d[2*i]+2<2*d[i])return 0;return 1;}
int condZ(u64 B){return lagl(B)||lagl(mirror(B));}
/* Z' (the form proven in Lean, coReach_sparse): 2 max B <= N+1 and for every non-least y in B:
   #(B n [y, 2y-3]) <= #(B n [1, y-1]); or the mirror image */
static int spl(u64 B){int d[70];int n=elems(B,d);if(2*d[n-1]>N+1)return 0;
  for(int i=1;i<n;i++){int y=d[i],a=0,b=0;for(int j=0;j<n;j++){if(d[j]<y)a++; if(d[j]>=y&&d[j]+2<2*y)b++;} if(b>a)return 0;} return 1;}
int condS(u64 B){return spl(B)||spl(mirror(B));}
/* W: general dyadic (Lean coReach_dyadic): 2x <= y for x < y in B and the top two elements
   satisfy 2 d_k <= N + d_{k-1} + 2; or the mirror image */
static int dyg(u64 B){int d[70];int n=elems(B,d);for(int i=0;i+1<n;i++)if(d[i+1]<2*d[i])return 0;
  if(n>=2 && 2*d[n-1]>N+d[n-2]+2)return 0; return 1;}
int condW(u64 B){return dyg(B)||dyg(mirror(B));}
int condU(u64 B){return condA(B)||condS(B)||condW(B);}
/* H: Theorem G with the centre at an end of B: I >= 0 at every free m > min B, or
   I <= 0 at every free m < max B */
static int anch(u64 B){int mn=__builtin_ctzll(B)+1; for(int m=mn+1;m<=N;m++){if(B>>(m-1)&1)continue; if(imb(B,m)<0)return 0;} return 1;}
int condH(u64 B){return anch(B)||anch(mirror(B));}
/* E: the explicit anchored condition (Lean coReach_anchored): for every non-least y in B,
   (i) #(B n [y, 2y-3]) <= #(B n [1, y-1]), and (ii) if 2y >= N+4,
   #(B n [y, N]) <= #(B n [2y-N-2, y-1]); or the same for the mirror image */
static int anchE(u64 B){int d[70];int n=elems(B,d);
  for(int i=1;i<n;i++){int y=d[i],below=0,c1=0,c2=0,c3=0;
    for(int j=0;j<n;j++){if(d[j]<y)below++; if(d[j]>=y&&d[j]<=2*y-3)c1++; if(d[j]>=y)c2++; if(d[j]<y&&d[j]>=2*y-N-2)c3++;}
    if(c1>below)return 0; if(2*y>=N+4&&c2>c3)return 0;}
  return 1;}
int condE(u64 B){return anchE(B)||anchE(mirror(B));}
int condV(u64 B){return condA(B)||condE(B);}

/* hash set of k-sets */
#define SB 22
static u64 *sk; static int *scnt;
static int sidx(u64 s){size_t h=(s*0x9E3779B97F4A7C15ull)>>(64-SB);while(sk[h]){if(sk[h]==s)return (int)h;h=(h+1)&((1ull<<SB)-1);}sk[h]=s;return (int)h;}
static long npref;
static void enumv(u64 S,int depth){
  if(depth==K){scnt[sidx(S)]++;npref++;return;}
  for(int m=1;m<=N;m++){if(S>>(m-1)&1)continue;if(imb(S,m)==0)enumv(S|1ull<<(m-1),depth+1);}
}
static long bad[9];
static void allsets(u64 S,int start,int depth){
  if(depth==K){ int g=inwardG(S); if(condA(S)&&!g)bad[0]++; if(condY(S)&&!g)bad[1]++; if(condZ(S)&&!g)bad[2]++; if(condS(S)!=condZ(S))bad[3]++; if(condS(S)&&!g)bad[4]++; if(condW(S)&&!g)bad[5]++; if(condE(S)&&!g)bad[6]++; if(condU(S)&&!condE(S))bad[7]++; return;}
  for(int m=start;m<=N;m++)allsets(S|1ull<<(m-1),m+1,depth+1);
}
int main(int argc,char**argv){
  N=atoi(argv[1]); K=atoi(argv[2]); int verbose=argc>3?atoi(argv[3]):0; int nodfs=argc>4;
  FULL=(N==64)?~0ull:((1ull<<N)-1);
  for(int m=1;m<=N;m++){int r=reachv(m);L[m]=R[m]=0;for(int d=1;d<=r;d++){L[m]|=1ull<<(m-d-1);R[m]|=1ull<<(m+d-1);}}
  ht=malloc(sizeof(u64)<<HB); hmask=(1ull<<HB)-1;
  sk=calloc(1ull<<SB,sizeof(u64)); scnt=calloc(1ull<<SB,sizeof(int));
  if(!nodfs)allsets(0,1,0);
  enumv(0,0);
  long nV=0,pV=0,nE=0,pE=0,nH=0,pH=0,nW=0,nU=0,pW=0,pU=0,ns=0,nA=0,nM=0,nY=0,nZ=0,nG=0,nG1=0,nw=0,nu=0, pA=0,pM=0,pY=0,pZ=0,pG=0,pG1=0,pw=0,pu=0;
  for(size_t h=0;h<(1ull<<SB);h++){ if(!sk[h])continue; u64 B=sk[h]; long c=scnt[h]; ns++;
    int g=inwardG(B);
    if(condA(B)){nA++;pA+=c;} if(condM(B)){nM++;pM+=c;} if(condY(B)){nY++;pY+=c;} if(condZ(B)){nZ++;pZ+=c;} if(condW(B)){nW++;pW+=c;} if(condU(B)){nU++;pU+=c;} if(condH(B)){nH++;pH+=c;} if(condE(B)){nE++;pE+=c;} if(condV(B)){nV++;pV+=c;}
    if(g){nG++;pG+=c; if(verbose>1 && !condU(B)){int d[70];int n=elems(B,d);printf("GnotU");for(int i=0;i<n;i++)printf(" %d",d[i]);printf("\n");} continue;}
    if(nodfs)continue;
    if(gk(B,1)){nG1++;pG1+=c;continue;}
    if(witness(B)){nw++;pw+=c;} else {nu++;pu+=c; if(verbose){int d[70];int n=elems(B,d);printf("unres");for(int i=0;i<n;i++)printf(" %d",d[i]);printf("\n");}}
  }
  printf("N=%d k=%d prefixes=%ld sets=%ld | sets: A=%ld M=%ld Y=%ld Z=%ld W=%ld U=%ld H=%ld E=%ld V=%ld G=%ld G+1step=%ld dfs=%ld unresolved=%ld"
         " | prefixes: A=%ld M=%ld Y=%ld Z=%ld W=%ld U=%ld H=%ld E=%ld V=%ld G=%ld G+1=%ld dfs=%ld unresolved=%ld | allsets A!G=%ld Y!G=%ld Z!G=%ld S!=Z:%ld S!G=%ld W!G=%ld E!G=%ld U!E=%ld\n",
    N,K,npref,ns,nA,nM,nY,nZ,nW,nU,nH,nE,nV,nG,nG1,nw,nu,pA,pM,pY,pZ,pW,pU,pH,pE,pV,pG,pG1,pw,pu,bad[0],bad[1],bad[2],bad[3],bad[4],bad[5],bad[6],bad[7]);
  return 0;
}

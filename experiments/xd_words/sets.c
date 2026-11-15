// sets.c : reachable / live sets of the semi-symmetric fold problem, with word statistics.
//   ./sets N
// Bit i of S = panel i+1.  A step (S, m) is valid iff |S cap L(m)| = |S cap R(m)|.
// reach[S]: S is the set of a valid prefix.  co[S]: S can be completed.  live = both.
// For every S:  e(t) = N P(t) - s t  (t = 0..N),  J(m) = |S cap R(m)| - |S cap L(m)|.
// Output by size k: R, A, max_t |e| over all / reachable / live sets, max_m |J| likewise,
// and the necessary conditions
//   REM    : S has a removable element (m in S with J(m) = 0) or S is empty   [first order]
//   PK     : the sorted values |J(m)|, m in S, are dominated by 0,1,2,...     [parking]
//   REMADD : REM, and S has an addable element (m not in S, J(m) = 0) or S is full
//   PK2    : PK for the placed and for the unplaced panels                    [nec. for live]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint32_t u32;
int N; u32 Lm[40], Rm[40];
static inline int pc(u32 x){return __builtin_popcount(x);}
int main(int argc,char**argv){
  N=atoi(argv[1]); u32 full=(N==32)?~0u:((1u<<N)-1);
  for(int m=1;m<=N;m++){int r=(m-1<N-m)?m-1:N-m; Lm[m]=0;Rm[m]=0;
    for(int d=1;d<=r;d++){Lm[m]|=1u<<(m-d-1);Rm[m]|=1u<<(m+d-1);} }
  size_t tot=(size_t)1<<N;
  unsigned char*fl=calloc(tot,1); // bit0 reach, bit1 co
  fl[0]|=1;
  for(u32 S=1;;S++){ u32 T=S; while(T){int i=__builtin_ctz(T);T&=T-1; u32 S0=S&~(1u<<i); int m=i+1;
      if((fl[S0]&1)&&pc(S0&Lm[m])==pc(S0&Rm[m])){fl[S]|=1;break;} } if(S==full)break;}
  fl[full]|=2;
  for(u32 S=full-1;;S--){ u32 T=full&~S; while(T){int i=__builtin_ctz(T);T&=T-1; int m=i+1;
      if((fl[S|(1u<<i)]&2)&&pc(S&Lm[m])==pc(S&Rm[m])){fl[S]|=2;break;} } if(S==0)break;}
  static long long R[40],A[40],REM[40],PK[40],PK2[40],C[40],REMADD[40];
  static int mxe[3][40],mxJ[3][40];
  for(u32 S=0;;S++){
    int s=pc(S); int cls=(fl[S]==3)?2:((fl[S]&1)?1:0);
    C[s]++; if(fl[S]&1)R[s]++; if(fl[S]==3)A[s]++;
    int P=0,me=0; for(int t=1;t<=N;t++){P+=(S>>(t-1))&1; int e=N*P-s*t; if(e<0)e=-e; if(e>me)me=e;}
    int cntin[40],cntout[40]; memset(cntin,0,sizeof cntin); memset(cntout,0,sizeof cntout);
    int mJ=0,rem=0,add=0;
    for(int m=1;m<=N;m++){int J=pc(S&Rm[m])-pc(S&Lm[m]); if(J<0)J=-J; if(J>mJ)mJ=J;
      if((S>>(m-1))&1){cntin[J]++; if(J==0)rem=1;} else {cntout[J]++; if(J==0)add=1;}}
    int pk=1,acc=0; for(int i=0;i<s;i++){acc+=cntin[i]; if(acc<i+1){pk=0;break;}}
    int pko=1; acc=0; for(int i=0;i<N-s;i++){acc+=cntout[i]; if(acc<i+1){pko=0;break;}}
    if(rem||s==0)REM[s]++; if(pk)PK[s]++; if(pk&&pko)PK2[s]++; if((rem||s==0)&&(add||s==N))REMADD[s]++;
    for(int c=0;c<=cls;c++){ if(me>mxe[c][s])mxe[c][s]=me; if(mJ>mxJ[c][s])mxJ[c][s]=mJ; }
    if((fl[S]&1)&&!pk){printf("BUG reachable but not PK %u\n",S);}
    if(fl[S]==3&&!pko){printf("BUG live but not PK2 %u\n",S);}
    if(S==full)break;
  }
  long long tR=0,tA=0,tREM=0,tPK=0,tPK2=0,tRA=0;
  printf("# N=%d\n# k C(N,k) R A REM PK REMADD PK2 | max|e| all reach live (k(N-k)) | max|J| all reach live\n",N);
  for(int k=0;k<=N;k++){tR+=R[k];tA+=A[k];tREM+=REM[k];tPK+=PK[k];tPK2+=PK2[k];tRA+=REMADD[k];
    printf("%2d %lld %lld %lld %lld %lld %lld %lld | %d %d %d (%d) | %d %d %d\n",k,C[k],R[k],A[k],REM[k],PK[k],REMADD[k],PK2[k],
      mxe[0][k],mxe[1][k],mxe[2][k],k*(N-k),mxJ[0][k],mxJ[1][k],mxJ[2][k]);}
  printf("TOTAL N=%d 2^N=%zu R=%lld A=%lld REM=%lld PK=%lld REMADD=%lld PK2=%lld  R/2^N=%.4f A/2^N=%.4f REM/2^N=%.4f PK/2^N=%.4f REMADD/2^N=%.4f PK2/2^N=%.4f\n",
    N,tot,tR,tA,tREM,tPK,tRA,tPK2,(double)tR/tot,(double)tA/tot,(double)tREM/tot,(double)tPK/tot,(double)tRA/tot,(double)tPK2/tot);
  return 0;}

/* Test Claim A: if S has a valid ordering with <= j ascending runs, then for every n,
   |{m in S : M - m <= n}| <= B_j(n) := #{g in [1,n] : popcount(g) <= j}   (M = N+1).
   Mirror form (by RM symmetry) is the statement for the unplaced set near the left edge.
   usage: claimA N.  Reports violations and, for each j, the tightness. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int N; static uint32_t Lm[40], Rm[40];
static int valid(uint32_t S,int m){ return __builtin_popcount(S&Lm[m])==__builtin_popcount(S&Rm[m]); }
int main(int argc,char**argv){ N=atoi(argv[1]); int M=N+1;
  for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m; for(int d=1;d<=r;d++){Lm[m]|=1u<<(m-d-1); Rm[m]|=1u<<(m+d-1);} }
  uint32_t F=(1u<<N)-1; unsigned char *b=malloc((size_t)(F+1)*(N+1)); for(size_t i=0;i<(size_t)(F+1)*(N+1);i++) b[i]=255;
  b[0]=1; long viol[40]={0}, tight[40]={0}, cnt[40]={0}; static int T[8][40];
  for(uint32_t S=0;S<=F;S++){ int D=255;
    for(int l=0;l<=N;l++){ int v=b[(size_t)S*(N+1)+l]; if(v==255) continue; if(v<D) D=v; if(S==F) continue;
      for(int m=1;m<=N;m++){ if(S>>(m-1)&1) continue; if(!valid(S,m)) continue;
        int nv=v+(m<l); size_t j=(size_t)(S|(1u<<(m-1)))*(N+1)+m; if(nv<b[j]) b[j]=nv; } }
    if(D==255||S==0) continue; cnt[D]++;
    int c=0, B=0, bad=0, tt=0;
    for(int n=1;n<=N;n++){ int m=M-n; c += (S>>(m-1))&1; B += __builtin_popcount(n)<=D; if(c>B) bad=1; for(int jj=D;jj<8;jj++) if(c>T[jj][n]) T[jj][n]=c; if(c==B) tt=1; }
    if(bad){ if(viol[D]<3){ printf("violation D=%d: ",D); for(int m=1;m<=N;m++) putchar(S>>(m-1)&1?'#':'.'); printf("\n"); } viol[D]++; }
    if(tt) tight[D]++; }
  for(int j=1;j<=4;j++){ printf("T_%d(n), n=1..N:",j); for(int n=1;n<=N;n++){ int B=0; for(int g=1;g<=n;g++) B+=__builtin_popcount(g)<=j; printf(" %d%s",T[j][n], T[j][n]>B?"*":"");} printf("\n"); }
  printf("N=%d:",N); for(int j=1;j<=6;j++) if(cnt[j]) printf(" j=%d sets=%ld viol=%ld;",j,cnt[j],viol[j]); printf("\n");
  return 0; }

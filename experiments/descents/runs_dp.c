/* For every set S reachable by a valid ordering, D(S) = min number of ascending runs of a
   valid ordering of S (as a prefix).  Test candidate potentials against D.
   usage: runs_dp N.  Prints max of each candidate over sets with D(S) = j. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int N; static uint32_t Lm[40], Rm[40];
static int zblock(uint32_t S){ int a=0,b=0; while(a<N && (S>>a&1)) a++; while(b<N && (S>>(N-1-b)&1)) b++; if(a==N) return N+1; return a+b+1; }
static int longest_block(uint32_t S){ int best=0,cur=0; for(int i=0;i<N;i++){ if(S>>i&1){cur++; if(cur>best)best=cur;} else cur=0;} return best; }
int main(int argc,char**argv){ N=atoi(argv[1]);
  for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m; for(int d=1;d<=r;d++){Lm[m]|=1u<<(m-d-1); Rm[m]|=1u<<(m+d-1);} }
  uint32_t F=(1u<<N)-1; unsigned char *b=malloc((size_t)(F+1)*(N+1)); for(size_t i=0;i<(size_t)(F+1)*(N+1);i++) b[i]=255;
  b[0]=1;
  int maxB[40]={0}, maxZ[40]={0};
  for(uint32_t S=0;S<=F;S++){ int D=255;
    for(int l=0;l<=N;l++){ int v=b[(size_t)S*(N+1)+l]; if(v==255) continue; if(v<D) D=v;
      if(S==F) continue;
      for(int m=1;m<=N;m++){ if(S>>(m-1)&1) continue; if(__builtin_popcount(S&Lm[m])!=__builtin_popcount(S&Rm[m])) continue;
        int nv=v+(m<l); size_t j=(size_t)(S|(1u<<(m-1)))*(N+1)+m; if(nv<b[j]) b[j]=nv; } }
    if(D==255||S==0) continue;
    int B=longest_block(S); if(B>maxB[D]) maxB[D]=B; int Z=zblock(S); if(Z>maxZ[D]) maxZ[D]=Z; }
  printf("N=%d:",N); for(int j=1;j<=6;j++) printf(" D=%d blk=%d zblk=%d (2^(D+1)-1=%d);",j,maxB[j],maxZ[j],(2<<j)-1); printf("\n");
  return 0; }

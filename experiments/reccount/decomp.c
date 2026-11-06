/* decomp.c: decomposition statistics of semi-symmetric sequences.
   usage: decomp N [outdir]
   Bits: panel m <-> bit m-1.  Bal(S,m): |S ∩ L_m| = |S ∩ R_m|.
   copy:    Bal(S,x) for all x in S          (window copy of the |S|-strip)
   neutral: Bal(S,m) for all m in [1,N]      (S and S^c both copies)
   Prints a(N); counts of copies / neutral sets by size; I(N) (no proper nonempty neutral
   prefix); J(N) (no copy prefix of size 2..N-1); the first-neutral and first-copy
   decompositions.  Writes sets_N.txt (every proper neutral set: mask, size, g, gI, h)
   and copyJ_N.txt (range of gJ and g over the copies of each size). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static void pr(u128 x){char b[50];int i=49;b[i]=0;if(!x){printf("0");return;}while(x){b[--i]='0'+x%10;x/=10;}printf("%s",b+i);}
int main(int argc,char**argv){
  int N=atoi(argv[1]); const char*dir=argc>2?argv[2]:".";
  uint64_t full=(1ULL<<N)-1, M=1ULL<<N;
  uint64_t L[64],R[64];
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m;L[m]=R[m]=0;for(int d=1;d<=D;d++){L[m]|=1ULL<<(m-d-1);R[m]|=1ULL<<(m+d-1);}}
  uint8_t *fl=calloc(M,1); /* bit0 copy, bit1 neutral */
  for(uint64_t S=1;S<M;S++){int cp=1,nt=1;
    for(int m=1;m<=N;m++){int b=__builtin_popcountll(S&L[m])==__builtin_popcountll(S&R[m]);
      if(!b){nt=0; if(S>>(m-1)&1){cp=0;break;}}}
    fl[S]=cp|(nt<<1);}
  uint64_t *g=calloc(M,8),*gI=calloc(M,8),*gJ=calloc(M,8),*h=calloc(M,8);
  g[0]=gI[0]=gJ[0]=1;
  for(uint64_t S=0;S<full;S++){
    uint64_t c=g[S],cI=gI[S],cJ=gJ[S]; int k=__builtin_popcountll(S);
    if(S && (fl[S]&2)) cI=0;            /* proper nonempty neutral prefix: kill */
    if(k>=2 && (fl[S]&1)) cJ=0;          /* copy prefix of size 2..N-1: kill */
    if(!c)continue;
    for(int m=1;m<=N;m++){uint64_t b=1ULL<<(m-1);if(S&b)continue;
      if(__builtin_popcountll(S&L[m])!=__builtin_popcountll(S&R[m]))continue;
      g[S|b]+=c; gI[S|b]+=cI; gJ[S|b]+=cJ;}}
  h[full]=1;
  for(uint64_t S=full;S-->0;){uint64_t s=0;
    for(int m=1;m<=N;m++){uint64_t b=1ULL<<(m-1);if(S&b)continue;
      if(__builtin_popcountll(S&L[m])==__builtin_popcountll(S&R[m]))s+=h[S|b];}
    h[S]=s;}
  printf("N=%d a=%llu I=%llu J=%llu\n",N,(unsigned long long)g[full],(unsigned long long)gI[full],(unsigned long long)gJ[full]);
  long ncopy[64]={0},nneu[64]={0}; u128 firstNeu[64]={0},firstCopy[64]={0},copyMass[64]={0};
  for(uint64_t S=1;S<full;S++){int k=__builtin_popcountll(S);
    if(fl[S]&1){ncopy[k]++; if(k>=2) firstCopy[k]+=(u128)gJ[S]*h[S]; copyMass[k]+=(u128)g[S]*h[S];}
    if(fl[S]&2){nneu[k]++; firstNeu[k]+=(u128)gI[S]*h[S];}}
  printf("size #copies #neutral firstNeutralMass firstCopyMass copyPrefixMass\n");
  for(int k=1;k<N;k++){printf("%d %ld %ld ",k,ncopy[k],nneu[k]);pr(firstNeu[k]);printf(" ");pr(firstCopy[k]);printf(" ");pr(copyMass[k]);printf("\n");}
  char fn[256]; sprintf(fn,"%s/sets_%d.txt",dir,N); FILE*f=fopen(fn,"w");
  for(uint64_t S=1;S<full;S++) if(fl[S]&2) fprintf(f,"%llx %d %llu %llu %llu\n",(unsigned long long)S,__builtin_popcountll(S),(unsigned long long)g[S],(unsigned long long)gI[S],(unsigned long long)h[S]);
  fclose(f);
  sprintf(fn,"%s/copyJ_%d.txt",dir,N); f=fopen(fn,"w");
  for(int k=2;k<N;k++){uint64_t mn=~0ULL,mx=0,gm=~0ULL,gx=0;
    for(uint64_t S=1;S<full;S++) if(__builtin_popcountll(S)==k && (fl[S]&1)){if(gJ[S]<mn)mn=gJ[S];if(gJ[S]>mx)mx=gJ[S];if(g[S]<gm)gm=g[S];if(g[S]>gx)gx=g[S];}
    fprintf(f,"%d J[min,max]=%llu %llu g[min,max]=%llu %llu\n",k,(unsigned long long)mn,(unsigned long long)mx,(unsigned long long)gm,(unsigned long long)gx);}
  fclose(f);
  return 0;
}

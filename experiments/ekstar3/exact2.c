/* exact2.c NMAX: tests the "end extension" relation
     H1:  S subset [N-1], CoReach_{N-1}(S)  ->  CoReach_N(S)
   over ALL subsets S (and by size), and the shifted version H1' (S + 1). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned int u32;
static unsigned char *cr[27];
static void compute(int N){ u32 full=((1u<<N)-1); cr[N]=malloc((size_t)1<<N);
  u32 Lm[33],Rm[33]; for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m;Lm[m]=Rm[m]=0;for(int d=1;d<=r;d++){Lm[m]|=1u<<(m-d-1);Rm[m]|=1u<<(m+d-1);}}
  for(long s=full;s>=0;s--){ u32 S=(u32)s; if(S==full){cr[N][S]=1;continue;} int ok=0;
    for(int m=1;m<=N&&!ok;m++){ if(S>>(m-1)&1)continue; if(__builtin_popcount(S&Lm[m])==__builtin_popcount(S&Rm[m])&&cr[N][S|1u<<(m-1)])ok=1;}
    cr[N][S]=ok; }
}
int main(int argc,char**argv){ int NM=atoi(argv[1]); int ksz=argc>2?atoi(argv[2]):-1;
  for(int N=3;N<=NM;N++)compute(N);
  for(int N=4;N<=NM;N++){ long cnt[33]={0},fail[33]={0}; int shown=0;
    for(u32 S=0;S<(1u<<(N-1));S++){ if(!cr[N-1][S])continue; int k=__builtin_popcount(S); cnt[k]++;
      if(!cr[N][S]){fail[k]++; if(shown<4 && (ksz<0||k==ksz)){shown++;printf("  fail N=%d:",N);for(int x=1;x<N;x++)if(S>>(x-1)&1)printf(" %d",x);printf("\n");}}}
    printf("N=%d",N); for(int k=0;k<N;k++)if(fail[k])printf(" k%d:%ld/%ld",k,fail[k],cnt[k]); printf("\n");
  }
}

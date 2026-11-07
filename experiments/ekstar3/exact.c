/* exact.c NMAX: exact co-reachability of every subset of [N], N <= NMAX (<= 24), by DP in the
   background form (S co-reachable iff S = [N] or some free m valid on S has S + m co-reachable).
   Tests candidate relations between strips N-1, N-2 and N for 3-sets (see PROOFS.txt). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned int u32;
static unsigned char *cr[26];
static void compute(int N){ u32 full=(N==32)?~0u:((1u<<N)-1); cr[N]=malloc((size_t)1<<N);
  u32 Lm[33],Rm[33]; for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m;Lm[m]=Rm[m]=0;for(int d=1;d<=r;d++){Lm[m]|=1u<<(m-d-1);Rm[m]|=1u<<(m+d-1);}}
  for(long s=full;s>=0;s--){ u32 S=(u32)s; if(S==full){cr[N][S]=1;continue;} int ok=0;
    for(int m=1;m<=N&&!ok;m++){ if(S>>(m-1)&1)continue; if(__builtin_popcount(S&Lm[m])==__builtin_popcount(S&Rm[m])&&cr[N][S|1u<<(m-1)])ok=1;}
    cr[N][S]=ok; }
}
#define BIT(x) (1u<<((x)-1))
int main(int argc,char**argv){ int NM=atoi(argv[1]);
  for(int N=3;N<=NM;N++)compute(N);
  for(int N=5;N<=NM;N++){ long tot=0,dead=0,h1=0,h1f=0,h2=0,h2f=0,h3=0,h3f=0;
    for(int a=2;a<=N-1;a++)for(int b=a+1;b<=N-1;b++)for(int c=b+1;c<=N-1;c++){ tot++;
      u32 D=BIT(a)|BIT(b)|BIT(c); int r=cr[N][D]; if(!r){dead++;printf("DEAD N=%d %d %d %d\n",N,a,b,c);}
      /* H1: D inside [N-1] (c <= N-2): CoReach_{N-1}(D) -> CoReach_N(D) */
      if(c<=N-2){ if(cr[N-1][D]){h1++; if(!r)h1f++;} }
      /* H2: shift into [N-2]: CoReach_{N-2}(D-1) -> CoReach_N(D) */
      { u32 E=BIT(a-1)|BIT(b-1)|BIT(c-1); if(cr[N-2][E]){h2++; if(!r)h2f++;} }
      /* H3: CoReach_{N-1}(D + {N-1})?  (c <= N-2) */
      if(c<=N-2){ if(cr[N-1][D|BIT(N-1)]){h3++; if(!r)h3f++;} }
    }
    printf("N=%d tot=%ld dead=%ld H1 %ld/%ld fail, H2 %ld/%ld, H3 %ld/%ld\n",N,tot,dead,h1f,h1,h2f,h2,h3f,h3);
  }
}

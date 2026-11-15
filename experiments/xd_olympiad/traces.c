/* traces.c : commutation classes of valid sequences by Cartier-Foata inclusion-exclusion.
   x,y commute (far) iff |x-y| > max(r_x, r_y).  t(S) = #valid classes with content S:
     t(S) = sum_{c in S, step (S\c, c) valid} t(S\c)
          - sum_{far pairs {x,y} in S, both steps valid} t(S\{x,y})
   (cliques of the commutation graph have size <= 2: two panels of the same half never commute).
   usage: traces N [chains]
   prints tau(N) = t([N]); with "chains" (N <= 22) also Z(N) = #valid sequences in which no two
   consecutive panels commute (classes of size 1). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef __int128 i128;
static void pr(i128 x){ char b[64]; int n=0,neg=0; if(x<0){neg=1;x=-x;} if(x==0)b[n++]='0'; while(x>0){b[n++]='0'+(int)(x%10);x/=10;} if(neg)putchar('-'); while(n--)putchar(b[n]); }
int main(int argc,char**argv){
  int N=atoi(argv[1]); int chains=argc>2;
  uint32_t L[40],R[40],farm[40]; int r[40];
  for(int m=1;m<=N;m++){ r[m]=m-1<N-m?m-1:N-m; L[m]=R[m]=0; for(int d=1;d<=r[m];d++){L[m]|=1u<<(m-d-1);R[m]|=1u<<(m+d-1);} }
  for(int x=1;x<=N;x++){ farm[x]=0; for(int y=1;y<=N;y++){ int d=abs(x-y); if(x!=y&&d>r[x]&&d>r[y]) farm[x]|=1u<<(y-1);} }
  uint32_t full=(1u<<N)-1; size_t sz=(size_t)1<<N;
  i128 *t=calloc(sz,sizeof(i128)); t[0]=1;
  for(uint32_t S=1;;S++){ uint32_t val=0;
    for(int m=1;m<=N;m++){ uint32_t b=1u<<(m-1); if(!(S&b))continue; uint32_t P=S&~b;
      if(__builtin_popcount(P&L[m])==__builtin_popcount(P&R[m])) val|=b; }
    i128 s=0;
    for(uint32_t v=val;v;v&=v-1){ int x=__builtin_ctz(v); s+=t[S&~(1u<<x)];
      for(uint32_t w=val&farm[x+1]&~((2u<<x)-1);w;w&=w-1){ int y=__builtin_ctz(w); s-=t[S&~(1u<<x)&~(1u<<y)]; } }
    t[S]=s; if(S==full)break; }
  printf("N %d tau ",N); pr(t[full]); printf("\n");
  if(chains&&N<=22){ /* z[S][last] */
    uint64_t *z=calloc(sz*(size_t)N,8);
    for(int m=1;m<=N;m++) z[((size_t)1<<(m-1))*N+(m-1)]=1;
    for(uint32_t S=1;S<full;S++){ for(int l=0;l<N;l++){ uint64_t c=z[(size_t)S*N+l]; if(!c)continue;
        for(int m=1;m<=N;m++){ uint32_t b=1u<<(m-1); if(S&b)continue; if(farm[l+1]&b)continue;
          if(__builtin_popcount(S&L[m])!=__builtin_popcount(S&R[m]))continue;
          z[(size_t)(S|b)*N+(m-1)]+=c; } } }
    uint64_t tot=0; for(int l=0;l<N;l++)tot+=z[(size_t)full*N+l];
    printf("N %d chains %llu\n",N,(unsigned long long)tot); }
  return 0;
}

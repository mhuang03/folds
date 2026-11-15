/* Offset strips / interval counts.
   a(N; al, be) = number of orderings of panels 1..N such that at every step, with S the
   earlier set and m the new panel, r = min(m-1+al, N-m+be):
        #{d<=r : m-d in S} = #{d<=r : m+d in S}        (panels outside [1,N] never placed)
   This equals G_M(i,j) = g_M([i,j]) with M = N+al+be, i = al+1, j = al+N.
   usage: off N al be          -> prints a(N;al,be)
          off N row al        -> prints a(N;al,be) for be = 0..N-1
          off N table [amax]   -> prints all a(N;al,be), 0<=al<=be<=amax (default N-1; the
                                  values stabilise once al or be >= N-1); "-" for be<al
                                  (mirror symmetric)
   unsigned __int128 counts. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static void pr(u128 x){ char b[64]; int k=0; if(!x){printf("0");return;} while(x){b[k++]='0'+(int)(x%10);x/=10;} while(k--)putchar(b[k]); }
static u128 *g;
static u128 run(int N,int al,int be){
  uint32_t L[40],R[40]; uint32_t full=(N==32)?0xffffffffu:((1u<<N)-1);
  for(int m=1;m<=N;m++){ int r=(m-1+al<N-m+be)?m-1+al:N-m+be; L[m]=R[m]=0;
    for(int d=1;d<=r;d++){ if(m-d>=1)L[m]|=1u<<(m-d-1); if(m+d<=N)R[m]|=1u<<(m+d-1);} }
  memset(g,0,sizeof(u128)*((size_t)1<<N)); g[0]=1;
  for(uint32_t S=0;S<full;S++){ u128 c=g[S]; if(!c)continue;
    for(int m=1;m<=N;m++){ uint32_t b=1u<<(m-1); if(S&b)continue;
      if(__builtin_popcount(S&L[m])==__builtin_popcount(S&R[m])) g[S|b]+=c; } }
  return g[full];
}
int main(int argc,char**argv){
  int N=atoi(argv[1]);
  g=malloc(sizeof(u128)*((size_t)1<<N));
  if(!strcmp(argv[2],"table")){
    int amax=argc>3?atoi(argv[3]):N-1; if(amax<0)amax=0;
    for(int al=0;al<=amax;al++){ for(int be=0;be<=amax;be++){
        if(be<al){ printf("- "); } else { pr(run(N,al,be)); printf(" "); } }
      printf("\n"); fflush(stdout);} }
  else if(!strcmp(argv[2],"row")){ int al=atoi(argv[3]);
    for(int be=0;be<=N-1;be++){ pr(run(N,al,be)); printf(" "); fflush(stdout);} printf("\n"); }
  else { pr(run(N,atoi(argv[2]),atoi(argv[3]))); printf("\n"); }
  return 0;
}

/* enumerate all valid (semi-symmetric) sequences of [1..N]; write raw bytes (N per seq)
   to stdout.  usage: enum N > file.  Prunes with completability (reverse reachability). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int N; static uint32_t Lm[40], Rm[40]; static unsigned char *comp; static unsigned char seq[40];
static int valid(uint32_t S,int m){ return __builtin_popcount(S&Lm[m])==__builtin_popcount(S&Rm[m]); }
static void rec(uint32_t S,int d){
  if(d==N){ fwrite(seq,1,N,stdout); return; }
  for(int m=1;m<=N;m++){ if(S>>(m-1)&1) continue; if(!valid(S,m)) continue;
    uint32_t T=S|(1u<<(m-1)); if(!comp[T]) continue; seq[d]=m; rec(T,d+1);} }
int main(int argc,char**argv){ N=atoi(argv[1]);
  for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m; for(int d=1;d<=r;d++){Lm[m]|=1u<<(m-d-1); Rm[m]|=1u<<(m+d-1);} }
  uint32_t F=(1u<<N)-1; comp=calloc(1u<<N,1); comp[F]=1;
  for(int64_t S=F; S>=0; S--){ if(comp[S]) continue; for(int m=1;m<=N;m++) if(!(S>>(m-1)&1) && valid((uint32_t)S,m) && comp[S|(1u<<(m-1))]){comp[S]=1;break;} }
  rec(0,0); return 0; }

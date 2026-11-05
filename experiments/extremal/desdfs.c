/* Find a semi-symmetric sequence with at most K-1 descents (K ascending runs) by DFS
   with a hash set of dead states (S, last, runs used).
   usage: desdfs N K [order]   order 0: try smaller panels first, 1: larger first.
   Prints the sequence or "none".  1 core. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int N, K, ORD; static uint64_t Lm[64], Rm[64];
static uint64_t *tab; static size_t cap, used;
static uint64_t hsh(uint64_t x){ x^=x>>33; x*=0xff51afd7ed558ccdULL; x^=x>>33; x*=0xc4ceb9fe1a85ec53ULL; x^=x>>33; return x; }
static int dead(uint64_t k){ size_t i=hsh(k)&(cap-1); while(tab[i]){ if(tab[i]==k) return 1; i=(i+1)&(cap-1);} return 0; }
static void mark(uint64_t k){ if(used*2>cap) return; size_t i=hsh(k)&(cap-1); while(tab[i]){ if(tab[i]==k) return; i=(i+1)&(cap-1);} tab[i]=k; used++; }
static int seq[64];
static int valid(uint64_t S,int m){ return __builtin_popcountll(S&Lm[m])==__builtin_popcountll(S&Rm[m]); }
static int rec(uint64_t S, int depth, int last, int runs){
  if(depth==N) return 1;
  uint64_t key = (S<<0) ^ ((uint64_t)last<<50) ^ ((uint64_t)runs<<57) ^ 1;
  if(N<=48){ key = S | ((uint64_t)last<<48) | ((uint64_t)runs<<56); }
  if(dead(key)) return 0;
  for(int ii=1; ii<=N; ii++){ int m = ORD? N+1-ii : ii;
    if(S>>(m-1)&1) continue;
    int nr = runs + (m<last);
    if(nr>K) continue;
    if(!valid(S,m)) continue;
    seq[depth]=m;
    if(rec(S|(1ULL<<(m-1)), depth+1, m, nr)) return 1;
  }
  mark(key); return 0;
}
int main(int argc,char**argv){
  N=atoi(argv[1]); K=atoi(argv[2]); ORD=argc>3?atoi(argv[3]):0;
  for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m; Lm[m]=Rm[m]=0;
    for(int d=1;d<=r;d++){Lm[m]|=1ULL<<(m-d-1); Rm[m]|=1ULL<<(m+d-1);} }
  cap=1ULL<<26; tab=calloc(cap,8);
  if(rec(0,0,0,1)){ printf("N=%d K=%d:",N,K); for(int i=0;i<N;i++) printf(" %d%s",seq[i],(i+1<N&&seq[i]>seq[i+1])?" |":""); printf("\n"); }
  else printf("N=%d K=%d: none (dead states %zu)\n",N,K,used);
  return 0; }

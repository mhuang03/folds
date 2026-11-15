/* Enumerate all semi-symmetric fold sequences of length N.
   usage: enum N > out.bin     writes a(N) records of N bytes (panels 1..N in step order). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int N; static uint64_t L[64],R[64],full; static unsigned char seq[64];
static unsigned char *buf; static size_t bl=0, cap=1<<24; static unsigned long long cnt=0;
static void rec(uint64_t S,int k){
  if(S==full){ if(bl+N>cap){fwrite(buf,1,bl,stdout);bl=0;} for(int i=0;i<N;i++)buf[bl++]=seq[i]; cnt++; return; }
  for(int m=1;m<=N;m++){ uint64_t b=1ULL<<(m-1); if(S&b)continue;
    if(__builtin_popcountll(S&L[m])!=__builtin_popcountll(S&R[m]))continue;
    seq[k]=m; rec(S|b,k+1);} }
int main(int argc,char**argv){ N=atoi(argv[1]); full=(1ULL<<N)-1; buf=malloc(cap);
  for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m;L[m]=R[m]=0;
    for(int d=1;d<=r;d++){L[m]|=1ULL<<(m-d-1);R[m]|=1ULL<<(m+d-1);}}
  rec(0,0); fwrite(buf,1,bl,stdout); fprintf(stderr,"N=%d count=%llu\n",N,cnt); return 0; }

/* pathdef.c -- deficit sum_k log((N-k)/V(S_k)) along explicit valid sequences.
   usage: ./pathdef N kind.  kind 0: bit-reversal order of positions (N = 2^L),
   kind 1: truncated bit-reversal (any N): sort panels by bit-reversed (m-1) in L=ceil(log2 N) bits.
   Checks validity and prints the deficit (tree-bound path product). */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
int N;
int main(int argc,char**argv){ N=atoi(argv[1]); int kind=atoi(argv[2]);
  int L=0; while((1<<L)<N) L++;
  int *ord=malloc(sizeof(int)*N), n=0;
  for(int i=0;i<(1<<L);i++){ int r=0; for(int b=0;b<L;b++) if(i>>b&1) r|=1<<(L-1-b); if(r<N) ord[n++]=r+1; }
  int *J=calloc(N+2,sizeof(int)); char*in=calloc(N+2,1); double def=0; int ok=1;
  for(int k=0;k<N;k++){ int V=0; for(int m=1;m<=N;m++) if(!in[m]&&J[m]==0) V++;
    int x=ord[k]; if(J[x]!=0) ok=0;
    def+=log((double)(N-k)/V);
    in[x]=1; for(int q=x/2+1;q<x;q++) J[q]++; for(int q=x+1;q<=(N+x)/2;q++) J[q]--; }
  printf("N=%d valid=%d deficit=%.3f deficit/N=%.4f\n",N,ok,def,def/N); return 0; }

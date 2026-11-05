/* Layered, mirror-halved version of selfdual.c (same output), for larger N.
   Layer k = partial transversals using k of the n = floor(N/2) pairs.
   State index = colexrank(P) * 2^(k-1) + (sign bits >> 1), canonical = smallest chosen
   pair takes its LEFT panel (mirror symmetry g(sigma T) = g(T)).
   Memory: two layers, max_k C(n,k) 2^(k-1) * 8 bytes  (~1.8 GB total for n = 19).
   usage: selfdual2 N */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static uint64_t C[64][64];
int main(int argc,char**argv){
  int N=atoi(argv[1]); int n=N/2;
  if(n<1){printf("%d 1\n",N);return 0;}
  for(int i=0;i<64;i++){C[i][0]=1;for(int j=1;j<=i;j++)C[i][j]=C[i-1][j-1]+(j<=i-1?C[i-1][j]:0);}
  uint64_t L[64],R[64];
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m;L[m]=R[m]=0;
    for(int d=1;d<=D;d++){L[m]|=1ULL<<(m-d-1);R[m]|=1ULL<<(m+d-1);}}
  /* layer 1: pair j with left panel, all canonical, g=1 if valid (empty S always valid) */
  uint64_t maxsz=0; for(int k=1;k<=n;k++){uint64_t s=C[n][k]<<(k-1); if(s>maxsz)maxsz=s;}
  uint64_t *cur=calloc(maxsz,8), *nxt=calloc(maxsz,8);
  if(!cur||!nxt){fprintf(stderr,"oom\n");return 1;}
  for(int j=0;j<n;j++) cur[C[j][1]]=1; /* colex rank of {j} = C(j,1) = j */
  int overflow=0;
  for(int k=1;k<n;k++){
    uint64_t nsz=C[n][k+1]<<k; memset(nxt,0,nsz*8);
    /* enumerate k-subsets in colex order */
    int p[64]; for(int i=0;i<k;i++)p[i]=i;
    for(uint64_t r=0;r<C[n][k];r++){
      /* precompute for each j not in P: new rank and insertion pos */
      uint64_t inP=0; for(int i=0;i<k;i++)inP|=1ULL<<p[i];
      uint64_t nr[64]; int pos[64];
      for(int j=0;j<n;j++) if(!(inP>>j&1)){
        int ps=0; while(ps<k&&p[ps]<j)ps++; pos[j]=ps;
        uint64_t rr=C[j][ps+1]; for(int i=0;i<k;i++) rr+=C[p[i]][i<ps?i+1:i+2]; nr[j]=rr; }
      for(uint64_t sb=0;sb<(1ULL<<(k-1));sb++){
        uint64_t c=cur[(r<<(k-1))+sb]; if(!c)continue;
        uint64_t signs=sb<<1; /* bit i: sign of p[i], 0 = left */
        uint64_t S=0; for(int i=0;i<k;i++){ if(signs>>i&1) S|=1ULL<<(N-p[i]-1); else S|=1ULL<<p[i]; }
        for(int j=0;j<n;j++) if(!(inP>>j&1)){
          for(int sg=0;sg<2;sg++){
            int m= sg? N-j : j+1;
            if(__builtin_popcountll(S&L[m])!=__builtin_popcountll(S&R[m])) continue;
            int ps=pos[j];
            uint64_t ns=(signs&((1ULL<<ps)-1)) | ((uint64_t)sg<<ps) | ((signs>>ps)<<(ps+1));
            if(ns&1) ns=(~ns)&((1ULL<<(k+1))-1); /* canonicalize by mirror */
            uint64_t *t=&nxt[(nr[j]<<k)+(ns>>1)]; if(*t+c<c)overflow=1; *t+=c;
          }
        }
      }
      /* next colex combination */
      int i=0; while(i<k-1 && p[i]+1==p[i+1]){p[i]=i;i++;} p[i]++;
    }
    uint64_t*tmp=cur;cur=nxt;nxt=tmp;
  }
  unsigned __int128 res=0;
  for(uint64_t sb=0;sb<(1ULL<<(n-1));sb++){ uint64_t c=cur[sb]; if(!c)continue;
    if(N%2){ uint64_t signs=sb<<1,S=0; for(int i=0;i<n;i++){ if(signs>>i&1) S|=1ULL<<(N-i-1); else S|=1ULL<<i; }
      int m=n+1; if(__builtin_popcountll(S&L[m])!=__builtin_popcountll(S&R[m])) continue; }
    res+=2*(unsigned __int128)c; }
  char buf[64]; int q=63; buf[q]=0; if(!res)buf[--q]='0'; while(res){buf[--q]='0'+(int)(res%10);res/=10;}
  printf("%d %s%s\n",N,buf+q,overflow?" OVERFLOW":"");
  return 0;
}

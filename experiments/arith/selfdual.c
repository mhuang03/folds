/* Count fold sequences fixed by reversal∘mirror (a_{N+1-k} = N+1-a_k), "self-dual".
   Such a sequence is determined by its first n = floor(N/2) steps, which pick exactly one
   panel from each pair {j, N+1-j}; for odd N the middle panel comes at step n+1.
   Step k is valid iff step N+1-k is (complement lemma + mirror), so only the first half
   (and the middle step) need checking.  State space: partial transversals, 3^n states.
   usage: selfdual N      prints "N c(N)" */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc,char**argv){
  int N=atoi(argv[1]); int n=N/2;
  uint64_t L[64],R[64];
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m;L[m]=R[m]=0;
    for(int d=1;d<=D;d++){L[m]|=1ULL<<(m-d-1);R[m]|=1ULL<<(m+d-1);}}
  uint64_t P3[40]; P3[0]=1; for(int i=1;i<=n;i++)P3[i]=P3[i-1]*3;
  uint64_t tot=P3[n];
  uint64_t *g=calloc(tot,8); if(!g){fprintf(stderr,"oom\n");return 1;}
  g[0]=1; int dig[40]={0}; uint64_t S=0; int overflow=0;
  unsigned __int128 res=0;
  for(uint64_t idx=0;idx<tot;idx++){
    if(idx){ /* increment base-3 counter, update S */
      int j=0; while(dig[j]==2){ dig[j]=0; S&=~(1ULL<<(N-j-1)); j++; }
      if(dig[j]==0){dig[j]=1; S|=1ULL<<j;} else {dig[j]=2; S&=~(1ULL<<j); S|=1ULL<<(N-j-1);}
    }
    uint64_t c=g[idx]; if(!c) continue;
    int full=1;
    for(int j=0;j<n;j++) if(!dig[j]){ full=0;
      int m1=j+1, m2=N-j;
      if(__builtin_popcountll(S&L[m1])==__builtin_popcountll(S&R[m1])){uint64_t*t=&g[idx+P3[j]]; if(*t+c<c)overflow=1; *t+=c;}
      if(__builtin_popcountll(S&L[m2])==__builtin_popcountll(S&R[m2])){uint64_t*t=&g[idx+2*P3[j]]; if(*t+c<c)overflow=1; *t+=c;}
    }
    if(full){
      if(N%2==0) res+=c;
      else { int m=n+1; if(__builtin_popcountll(S&L[m])==__builtin_popcountll(S&R[m])) res+=c; }
    }
  }
  char buf[64]; int p=63; buf[p]=0; if(!res)buf[--p]='0'; while(res){buf[--p]='0'+(int)(res%10);res/=10;}
  printf("%d %s%s\n",N,buf+p,overflow?" OVERFLOW":"");
  return 0;
}

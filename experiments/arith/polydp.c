/* Subset DP for statistic generating polynomials of semi-symmetric fold sequences.
   usage: polydp N mode       mode = free | lrmax | des
     free : #steps whose window holds no earlier panel (r=0 steps count)    state S
     lrmax: #left-to-right maxima (m > max S)                                 state S
     des  : #descents                                                         state (S,last)
   prints "N mode c_0 c_1 ... c_{N}" */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc,char**argv){
  int N=atoi(argv[1]); const char*mode=argv[2]; int D=N+1;
  uint64_t full=(1ULL<<N)-1, L[64],R[64];
  for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m;L[m]=R[m]=0;
    for(int d=1;d<=r;d++){L[m]|=1ULL<<(m-d-1);R[m]|=1ULL<<(m+d-1);}}
  int des=!strcmp(mode,"des"), fr=!strcmp(mode,"free");
  uint64_t res[64]={0};
  if(!des){
    uint64_t *g=calloc((full+1)*D,8); if(!g){fprintf(stderr,"oom\n");return 1;}
    g[0]=1;
    for(uint64_t S=0;S<full;S++){ uint64_t*src=g+S*D; int nz=0; for(int i=0;i<D;i++)if(src[i]){nz=1;break;} if(!nz)continue;
      int top=S?64-__builtin_clzll(S):0; /* max panel in S */
      for(int m=1;m<=N;m++){uint64_t b=1ULL<<(m-1); if(S&b)continue;
        int a=__builtin_popcountll(S&L[m]), r=__builtin_popcountll(S&R[m]); if(a!=r)continue;
        int inc= fr ? (a==0) : (m>top);
        uint64_t*dst=g+(S|b)*D; for(int i=0;i+inc<D;i++) dst[i+inc]+=src[i]; } }
    memcpy(res,g+full*D,D*8);
  } else {
    /* g[(S*N + last)*D + k] */
    uint64_t *g=calloc((full+1)*N*(uint64_t)D,8); if(!g){fprintf(stderr,"oom\n");return 1;}
    for(int m=1;m<=N;m++) g[((1ULL<<(m-1))*N+(m-1))*D]=1;
    for(uint64_t S=1;S<full;S++) for(int l=0;l<N;l++){ if(!(S>>l&1))continue;
      uint64_t*src=g+(S*N+l)*D; int nz=0; for(int i=0;i<D;i++)if(src[i]){nz=1;break;} if(!nz)continue;
      for(int m=1;m<=N;m++){uint64_t b=1ULL<<(m-1); if(S&b)continue;
        if(__builtin_popcountll(S&L[m])!=__builtin_popcountll(S&R[m]))continue;
        int inc=(l+1>m);
        uint64_t*dst=g+((S|b)*N+(m-1))*D; for(int i=0;i+inc<D;i++) dst[i+inc]+=src[i]; } }
    for(int l=0;l<N;l++) for(int i=0;i<D;i++) res[i]+=g[(full*N+l)*D+i];
  }
  printf("%d %s",N,mode); for(int i=0;i<D;i++)printf(" %llu",(unsigned long long)res[i]); printf("\n");
  return 0;
}

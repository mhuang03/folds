#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static void pr(u128 x){char b[50];int i=49;b[i]=0;if(!x){printf("0");return;}while(x){b[--i]='0'+(int)(x%10);x/=10;}printf("%s",b+i);}
int main(int argc,char**argv){
  int N=atoi(argv[1]); int sym = argc>2;
  uint64_t full=(1ULL<<N)-1;
  u128 *c=calloc(1ULL<<N,sizeof(u128));
  uint64_t Lm[64],Rm[64];
  for(int m=1;m<=N;m++){int D=m-1<N-m?m-1:N-m; Lm[m]=0;Rm[m]=0;
    for(int d=1;d<=D;d++){Lm[m]|=1ULL<<(m-d-1);Rm[m]|=1ULL<<(m+d-1);} }
  c[0]=1; uint64_t reach=0;
  for(uint64_t S=0;S<full;S++){ if(!c[S])continue; reach++;
    for(int m=1;m<=N;m++){ uint64_t b=1ULL<<(m-1); if(S&b)continue;
      int ok;
      if(sym){ /* mirror check */ uint64_t l=S&Lm[m], r=S&Rm[m]; ok=1;
        int D=m-1<N-m?m-1:N-m; for(int d=1;d<=D&&ok;d++) ok = (((l>>(m-d-1))&1)==((r>>(m+d-1))&1)); }
      else ok = __builtin_popcountll(S&Lm[m])==__builtin_popcountll(S&Rm[m]);
      if(ok) c[S|b]+=c[S]; } }
  printf("%d ",N); pr(c[full]); printf(" reachable=%llu\n",(unsigned long long)reach+1);
}

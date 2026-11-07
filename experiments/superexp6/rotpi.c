// For each d and rho in [0,d): count pi in V_d (valid d-strip sequences) such that
// mu o pi is also valid, mu(s) = (rho + 1 - s) mod* d.  (Generalised composition:
// residue classes mod d of the N-strip, N = d m + rho, in class order pi.)
#include <stdio.h>
#include <stdlib.h>
static int d; static long cnt[64]; static int a[64]; static int firstok[64][64];
static int valid(unsigned long S,int m,int n){ int r = m-1 < n-m ? m-1 : n-m; int l=0,rr=0;
  for(int k=1;k<=r;k++){ l+=(S>>(m-k))&1; rr+=(S>>(m+k))&1; } return l==rr; }
static int mu(int s,int rho){ int v=((rho+1-s)%d+d)%d; return v==0?d:v; }
static void dfs(int k,unsigned long S){
  if(k==d){ for(int rho=0;rho<d;rho++){ unsigned long T=0; int ok=1; for(int i=0;i<d&&ok;i++){ int t=mu(a[i],rho); if(!valid(T,t,d)) ok=0; T|=1UL<<t; }
      if(ok){ if(cnt[rho]==0) for(int i=0;i<d;i++) firstok[rho][i]=a[i]; cnt[rho]++; } } return; }
  for(int m=1;m<=d;m++) if(!((S>>m)&1)&&valid(S,m,d)){ a[k]=m; dfs(k+1,S|1UL<<m); }
}
int main(int argc,char**argv){ for(d=2; d<=atoi(argv[1]); d++){ for(int r=0;r<64;r++) cnt[r]=0; dfs(0,0);
  printf("d=%2d:",d); for(int rho=0;rho<d;rho++) printf(" %ld",cnt[rho]); printf("\n");
  for(int rho=0;rho<d;rho++){ printf("   rho=%d first:",rho); if(cnt[rho]) for(int i=0;i<d;i++) printf(" %d",firstok[rho][i]); printf("\n"); } } }

// count pi in V_d such that rot_r o pi in V_d for every r (rot_r(s) = (s-1+r) mod d + 1)
#include <stdio.h>
#include <stdlib.h>
static int d; static long cnt; static int a[64]; static int shown;
static int valid(unsigned long S,int m,int n){ int r = m-1 < n-m ? m-1 : n-m; int l=0,rr=0;
  for(int k=1;k<=r;k++){ l+=(S>>(m-k))&1; rr+=(S>>(m+k))&1; } return l==rr; }
static void dfs(int k,unsigned long S){
  if(k==d){ for(int r=1;r<d;r++){ unsigned long T=0; for(int i=0;i<d;i++){ int t=(a[i]-1+r)%d+1; if(!valid(T,t,d)) return; T|=1UL<<t; } }
    cnt++; if(shown<4){ shown++; printf("   "); for(int i=0;i<d;i++) printf(" %d",a[i]); printf("\n"); } return; }
  for(int m=1;m<=d;m++) if(!((S>>m)&1)&&valid(S,m,d)){ a[k]=m; dfs(k+1,S|1UL<<m); }
}
int main(int argc,char**argv){ for(d=2; d<=atoi(argv[1]); d++){ cnt=0; shown=0; dfs(0,0); printf("d=%d rotation-invariant: %ld\n",d,cnt); } }

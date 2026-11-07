// Odd d, rho in [0,d): search class orders pi of the form "pairs {s, mu(s)} placed
// consecutively" (mu(s) = (rho+1-s) mod* d, one fixed point placed alone) such that
// pi and mu o pi are both valid d-strip sequences.  Counts such pi.
#include <stdio.h>
#include <stdlib.h>
static int d,rho; static long cnt; static int a[64]; static int ex[64]; static int got;
static int valid(unsigned long S,int m){ int r = m-1 < d-m ? m-1 : d-m; int l=0,rr=0;
  for(int k=1;k<=r;k++){ l+=(S>>(m-k))&1; rr+=(S>>(m+k))&1; } return l==rr; }
static int mu(int s){ int v=((rho+1-s)%d+d)%d; return v==0?d:v; }
static int check(void){ unsigned long T=0; for(int i=0;i<d;i++){ int t=mu(a[i]); if(!valid(T,t)) return 0; T|=1UL<<t; } return 1; }
static void dfs(int k,unsigned long S){
  if(k==d){ if(check()){ cnt++; if(!got){got=1; for(int i=0;i<d;i++) ex[i]=a[i];} } return; }
  for(int s=1;s<=d;s++){ if((S>>s)&1) continue; int t=mu(s);
    if(t==s){ if(valid(S,s)){ a[k]=s; dfs(k+1,S|1UL<<s);} }
    else { if(valid(S,s) && valid(S|1UL<<s,t)){ a[k]=s; a[k+1]=t; dfs(k+2,S|1UL<<s|1UL<<t);} } }
}
int main(int argc,char**argv){ for(d=3; d<=atoi(argv[1]); d+=2){ printf("d=%d:",d); for(rho=0;rho<d;rho++){ cnt=0; got=0; dfs(0,0); printf(" %ld",cnt); }
  printf("\n"); } }

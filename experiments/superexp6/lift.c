// For each valid N-sequence, count "lifts": valid (N+1)-sequences obtained by
// inserting a new panel p (others relabelled m -> m + [m>=p]) at some time t.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int N;
static int valid(unsigned long S,int m,int n){ // panels 1..n, S bitmask bit m
  int r = m-1 < n-m ? m-1 : n-m; int l=0,rr=0;
  for(int d=1; d<=r; d++){ l += (S>>(m-d))&1; rr += (S>>(m+d))&1; }
  return l==rr;
}
static int seqvalid(int *b,int n){ unsigned long S=0; for(int i=0;i<n;i++){ if(!valid(S,b[i],n)) return 0; S|=1UL<<b[i]; } return 1; }
static int a[64]; static long cnt=0, nolift=0; static long hist[200]; static long hp[64];
static void test(void){
  int b[64]; int lifts=0; int pmask[64]; memset(pmask,0,sizeof pmask);
  for(int p=1;p<=N+1;p++) for(int t=0;t<=N;t++){
    int k=0; for(int i=0;i<t;i++) b[k++]=a[i]+(a[i]>=p); b[k++]=p; for(int i=t;i<N;i++) b[k++]=a[i]+(a[i]>=p);
    if(seqvalid(b,N+1)){ lifts++; pmask[p]=1; }
  }
  cnt++; if(!lifts) nolift++; hist[lifts<199?lifts:199]++;
  for(int p=1;p<=N+1;p++) if(pmask[p]) hp[p]++;
}
static void dfs(int k, unsigned long S){
  if(k==N){ test(); return; }
  for(int m=1;m<=N;m++) if(!((S>>m)&1) && valid(S,m,N)){ a[k]=m; dfs(k+1,S|1UL<<m); }
}
int main(int argc,char**argv){ N=atoi(argv[1]); dfs(0,0);
  printf("N=%d a=%ld nolift=%ld\n",N,cnt,nolift);
  printf("lift hist:"); for(int i=0;i<200;i++) if(hist[i]) printf(" %d:%ld",i,hist[i]); printf("\n");
  printf("p liftable:"); for(int p=1;p<=N+1;p++) printf(" %ld",hp[p]); printf("\n"); }

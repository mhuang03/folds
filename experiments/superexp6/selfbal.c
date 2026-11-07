// Self-balanced sets Z of the N-strip: every z in Z has equally many elements of Z in its
// two window arms.  Sub-block lemma: if W is balanced around every z in Z and Z is
// self-balanced, then g(W u Z) >= g(W) a(|Z|).  Chains [N] = Z1 u Z2 u ... with
// Z_i self-balanced and Z1..Z_{i-1} balanced around Z_i give a(N) >= prod a(|Z_i|).
// mode 0: list self-balanced sets by size (counts) and print those of size >= N/4.
// mode 1: search chains, report the best achievable size multiset (by sum of log a).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
static int N;
static int bal(unsigned S,int m){ int r = m-1 < N-m ? m-1 : N-m; int l=0,rr=0;
  for(int d=1; d<=r; d++){ l += (S>>(m-1-d))&1; rr += (S>>(m-1+d))&1; } return l==rr; }
static int selfbal(unsigned Z){ for(int m=1;m<=N;m++) if(((Z>>(m-1))&1) && !bal(Z&~(1u<<(m-1)),m)) return 0; return 1; }
static int balaround(unsigned W,unsigned Z){ for(int m=1;m<=N;m++) if(((Z>>(m-1))&1) && !bal(W,m)) return 0; return 1; }
static void pr(unsigned Z){ for(int m=1;m<=N;m++) putchar((Z>>(m-1))&1?'x':'.'); }
static double la[64];
static unsigned *sb; static int nsb;
static double best; static unsigned bestc[64]; static int bestr; static unsigned cur[64];
static void chain(unsigned W,int r,double val){
  unsigned full=(1u<<N)-1; unsigned R=full&~W;
  if(R==0){ if(val>best){best=val;bestr=r;memcpy(bestc,cur,sizeof cur);} return; }
  // upper bound prune: remaining as one block
  if(val+la[__builtin_popcount(R)]<=best) return;
  for(int i=0;i<nsb;i++){ unsigned Z=sb[i]; if((Z&W)||(Z&~R)) continue; // subset of R
    if(!balaround(W,Z)) continue; cur[r]=Z; chain(W|Z,r+1,val+la[__builtin_popcount(Z)]); }
}
int main(int argc,char**argv){ N=atoi(argv[1]); int mode=atoi(argv[2]);
  // ln a(n) for n<=40 from known values (semi_counts)
  const char* A[]={"1","1","2","4","10","28","96","256","1120","4256","17878","70960","383476","1620328","9167908","47821296","276182312","1481994716","10084180418","55082188120","398874108930","2505681033958","18168130281086","119006527671252","979730153850974","6564449510287388","55581983250573500","413109755332919448","3603074636066234798","27545080998591561856","262878496654501774250"};
  for(int i=0;i<=30;i++) la[i]=log(atof(A[i]));
  unsigned full=(1u<<N)-1; sb=malloc(sizeof(unsigned)*(1u<<N)); nsb=0;
  int cnt[64]={0};
  for(unsigned Z=1;Z<=full;Z++) if(Z!=full && selfbal(Z)){ cnt[__builtin_popcount(Z)]++; sb[nsb++]=Z; }
  printf("N=%d self-balanced counts by size:",N); for(int k=1;k<=N;k++) if(cnt[k]) printf(" %d:%d",k,cnt[k]); printf("\n");
  if(mode==0){ for(int i=0;i<nsb;i++) if(__builtin_popcount(sb[i])>=N/3){ pr(sb[i]); printf(" %d\n",__builtin_popcount(sb[i])); } }
  if(mode==2){ // sum over all chains of prod a(|Z_i|) (overcounts), DP over W
    double *Sm=calloc(1u<<N,sizeof(double)); Sm[0]=1;
    for(unsigned W=0;W<full;W++){ if(Sm[W]==0) continue; unsigned R=full&~W;
      for(int i=0;i<nsb;i++){ unsigned Z=sb[i]; if(Z&~R) continue; if(!balaround(W,Z)) continue;
        Sm[W|Z]+=Sm[W]*exp(la[__builtin_popcount(Z)]); } }
    printf("N=%d chain sum / a(N) = %.4f\n",N, Sm[full]/exp(la[N])); }
  if(mode==1){ // sort sb by size desc
    for(int i=0;i<nsb;i++) for(int j=i+1;j<nsb;j++) if(__builtin_popcount(sb[j])>__builtin_popcount(sb[i])){unsigned t=sb[i];sb[i]=sb[j];sb[j]=t;}
    best=-1; chain(0,0,0);
    printf("best chain: lnprod=%.3f  ln a(N)=%.3f  ratio=%.3f\n",best,la[N],best/la[N]);
    for(int i=0;i<bestr;i++){ pr(bestc[i]); printf(" %d\n",__builtin_popcount(bestc[i])); }
  }
}

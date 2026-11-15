/* Commutation (Cartier-Foata) classes of V_N.
   Panels x != y are INDEPENDENT iff |x-y| > max(reach x, reach y) (neither lies in the other's
   window); swapping two adjacent independent panels preserves semi-symmetry, swapping two
   adjacent dependent panels destroys it.  So V_N is a union of classes of the trace monoid.
   Reads data/V<N>.bin (N <= 15), maps every sequence to its lexicographically least
   commutation-equivalent word, and prints
     N  #classes  largest class  #singleton classes  sum of squares of class sizes
   plus (argument 2 = "check") the number of sequences whose canonical form is not in V_N. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;
static int cmp(const void*a,const void*b){u64 x=*(const u64*)a,y=*(const u64*)b;return x<y?-1:x>y;}
int main(int argc,char**argv){
  int N=atoi(argv[1]); char fn[256]; sprintf(fn,"%s/V%d.bin",argc>3?argv[3]:"data",N);
  FILE*f=fopen(fn,"rb"); if(!f){fprintf(stderr,"no file\n");return 1;}
  fseek(f,0,SEEK_END); long sz=ftell(f); fseek(f,0,SEEK_SET); long n=sz/N;
  unsigned char*buf=malloc(sz); if(fread(buf,1,sz,f)!=(size_t)sz)return 1; fclose(f);
  int ind[20][20]; int r[20];
  for(int m=1;m<=N;m++) r[m]=m-1<N-m?m-1:N-m;
  int npairs=0;
  for(int x=1;x<=N;x++)for(int y=1;y<=N;y++){int d=x>y?x-y:y-x; ind[x][y]=(x!=y)&&d>r[x]&&d>r[y]; if(x<y&&ind[x][y])npairs++;}
  u64*key=malloc(n*8), *orig=malloc(n*8);
  for(long i=0;i<n;i++){ unsigned char w[20]; memcpy(w,buf+i*N,N); int len=N; u64 k=0,o=0;
    for(int j=0;j<N;j++) o=o*16+(buf[i*N+j]-1);
    for(int step=0;step<N;step++){ int best=-1;
      for(int p=0;p<len;p++){ int ok=1; for(int q=0;q<p&&ok;q++) ok=ind[w[q]][w[p]];
        if(ok&&(best<0||w[p]<w[best])) best=p; }
      k=k*16+(w[best]-1); memmove(w+best,w+best+1,len-best-1); len--; }
    key[i]=k; orig[i]=o; }
  qsort(orig,n,8,cmp);
  long notin=0;
  if(argc>2&&!strcmp(argv[2],"check")) for(long i=0;i<n;i++) if(!bsearch(&key[i],orig,n,8,cmp)) notin++;
  qsort(key,n,8,cmp);
  long classes=0,maxc=0,single=0; double sq=0; long run=0;
  for(long i=0;i<n;i++){ run++; if(i==n-1||key[i+1]!=key[i]){classes++; if(run>maxc)maxc=run; if(run==1)single++; sq+=(double)run*run; run=0;} }
  printf("%d sequences=%ld independent-pairs=%d classes=%ld largest=%ld singletons=%ld sumsq=%.0f canonical-not-valid=%ld\n",N,n,npairs,classes,maxc,single,sq,notin);
  return 0; }

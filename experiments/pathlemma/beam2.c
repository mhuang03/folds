/* beam.c -- beam search for valid sequences with a large path product prod_k V(S_k).
   usage: ./beam N B [seed].  Prints log N! - max found sum log V (deficit) and deficit/N.
   J is kept incrementally (dipole lemma). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
int N, B, MODE;
static double G(int V,int f){ return MODE? (double)V/f : log((double)V); }
typedef struct { double sc; int *J; unsigned char *in; int V; int *hist; } St;
static uint64_t rs = 88172645463325252ULL;
static double rnd(void){ rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return (rs >> 11) * (1.0/9007199254740992.0); }
int cmp(const void*a,const void*b){ double x=((double*)a)[0], y=((double*)b)[0]; return x<y?1:x>y?-1:0; }
int main(int argc,char**argv){ N=atoi(argv[1]); B=atoi(argv[2]); MODE=getenv("LIN")?1:0; if(argc>3) rs+=atoi(argv[3])*7919ULL;
  St *cur=malloc(sizeof(St)*B), *nxt=malloc(sizeof(St)*B);
  for(int i=0;i<B;i++){ cur[i].J=calloc(N+2,sizeof(int)); cur[i].in=calloc(N+2,1); cur[i].hist=calloc(N+2,sizeof(int)); nxt[i].hist=calloc(N+2,sizeof(int)); nxt[i].J=calloc(N+2,sizeof(int)); nxt[i].in=calloc(N+2,1);}
  int nc=1; cur[0].sc=0;
  double *cand=malloc(sizeof(double)*3*(size_t)B*N);
  for(int k=0;k<N;k++){
    int nca=0;
    for(int i=0;i<nc;i++){ int V=0; for(int m=1;m<=N;m++) if(!cur[i].in[m] && cur[i].J[m]==0) V++;
      cur[i].V=V; if(!V) continue;
      for(int m=1;m<=N;m++) if(!cur[i].in[m] && cur[i].J[m]==0){
        /* lookahead: V of child */
        int x=m, V2=0;
        for(int q=1;q<=N;q++){ if(cur[i].in[q]||q==x) continue; int j=cur[i].J[q];
          if(q<x && x<=2*q-1) j++; else if(2*q-N<=x && x<q) j--; if(j==0) V2++; }
        if(k<N-1 && V2==0) continue;
        double s=cur[i].sc+G(V,N-k)+ (k<N-1? G(V2,N-k-1):0) + 1e-6*rnd();
        cand[3*nca]=s; cand[3*nca+1]=i; cand[3*nca+2]=m; nca++; }
    }
    if(!nca){ printf("N=%d B=%d died at k=%d\n",N,B,k); return 0; }
    qsort(cand,nca,3*sizeof(double),cmp);
    int nn= nca<B?nca:B;
    for(int t=0;t<nn;t++){ int i=(int)cand[3*t+1], x=(int)cand[3*t+2];
      memcpy(nxt[t].J,cur[i].J,sizeof(int)*(N+2)); memcpy(nxt[t].in,cur[i].in,N+2);
      nxt[t].sc=cur[i].sc+G(cur[i].V,N-k); nxt[t].in[x]=1; memcpy(nxt[t].hist,cur[i].hist,sizeof(int)*(N+2)); nxt[t].hist[k]=x;
      for(int q=1;q<=N;q++){ if(q<x && x<=2*q-1) nxt[t].J[q]++; else if(2*q-N<=x && x<q) nxt[t].J[q]--; }
    }
    St*tmp=cur;cur=nxt;nxt=tmp; nc=nn;
  }
  double best=-1; for(int i=0;i<nc;i++) if(cur[i].sc>best) best=cur[i].sc;
  if(argc>4){ int bi=0; for(int i=0;i<nc;i++) if(cur[i].sc>=best) bi=i;
    FILE*f=fopen(argv[4],"w"); for(int k=0;k<N;k++) fprintf(f,"%d\n",cur[bi].hist[k]); fclose(f); }
  double lf=lgamma(N+1.0);
  printf("N=%d B=%d sumlogV=%.3f logN!=%.3f deficit=%.3f deficit/N=%.4f\n",N,B,best,lf,lf-best,(lf-best)/N);
  return 0; }

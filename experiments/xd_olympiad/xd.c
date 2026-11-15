/* xd.c : subset DP with pluggable balance constraints, for the olympiad-toolkit experiments.
   usage: xd N mode [param]
   modes:
     semi        the full rule
     left        only panels m <= ceil(N/2) constrained  (left-half relaxation, middle included)
     leftx       only panels m <= floor(N/2)             (left half, middle excluded)
     outer P     only panels m <= P and m >= N+1-P       (outer relaxation)
     set MASK    only panels in the bitmask MASK (bit m-1) constrained
     del1        full rule on [N] AND full rule of the (N-1)-strip on the sequence with panel 1 deleted
     delN1       full rule on [N] AND (N-2)-strip rule after deleting panels 1 and N
     delmid      full rule on [N] AND (N-1)-strip rule after deleting panel ceil(N/2)
     only1       (N-1)-strip rule on panels 2..N only (panel 1 free): = N*a(N-1), sanity
   prints: total, signed total (sum of sgn), prefix counts T(k), reachable/alive/dead-end data,
           moves table M(k) = sum_{|S|=k} g(S) h(S) v(S) (h = completions, v = #valid moves),
           position table pos[m][k] (#sequences with panel m at step k). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef __int128 i128;
static void pr(i128 x){ char b[64]; int n=0,neg=0; if(x<0){neg=1;x=-x;} if(x==0)b[n++]='0'; while(x>0){b[n++]='0'+(int)(x%10);x/=10;} if(neg)putchar('-'); while(n--)putchar(b[n]); }
#define MAXC 4
static uint32_t CL[40][MAXC],CR[40][MAXC]; static int nc[40];
static int N;
static void addc(int m,uint32_t l,uint32_t r){ if(l==0&&r==0)return; CL[m][nc[m]]=l; CR[m][nc[m]]=r; nc[m]++; }
/* window of panel q in a strip of length n, embedded by label map lab[1..n] -> panel of [N] */
static void win(int n,int q,int *lab,uint32_t *l,uint32_t *r){ int D=q-1<n-q?q-1:n-q; *l=*r=0; for(int d=1;d<=D;d++){ *l|=1u<<(lab[q-d]-1); *r|=1u<<(lab[q+d]-1);} }
static inline int ok(uint32_t S,int m){ for(int i=0;i<nc[m];i++) if(__builtin_popcount(S&CL[m][i])!=__builtin_popcount(S&CR[m][i])) return 0; return 1; }
int main(int argc,char**argv){
  N=atoi(argv[1]); const char*mode=argv[2]; long par=argc>3?strtol(argv[3],0,0):0;
  int lab[40]; uint32_t l,r; uint32_t full=(1u<<N)-1;
  for(int i=1;i<=N;i++)lab[i]=i;
  for(int m=1;m<=N;m++){ int con=1;
    if(!strcmp(mode,"left")) con=(2*m<=N+1);
    if(!strcmp(mode,"leftx")) con=(2*m<=N);
    if(!strcmp(mode,"outer")) con=(m<=par||m>=N+1-par);
    if(!strcmp(mode,"set")) con=(par>>(m-1))&1;
    if(!strcmp(mode,"only1")) con=0;
    if(con){ win(N,m,lab,&l,&r); addc(m,l,r);} }
  if(!strcmp(mode,"del1")||!strcmp(mode,"only1")){ for(int i=1;i<=N-1;i++)lab[i]=i+1; for(int q=1;q<=N-1;q++){ win(N-1,q,lab,&l,&r); addc(lab[q],l,r);} }
  if(!strcmp(mode,"delN1")){ for(int i=1;i<=N-2;i++)lab[i]=i+1; for(int q=1;q<=N-2;q++){ win(N-2,q,lab,&l,&r); addc(lab[q],l,r);} }
  if(!strcmp(mode,"delmid")){ int c=(N+1)/2; for(int i=1;i<=N-1;i++)lab[i]=i<c?i:i+1; for(int q=1;q<=N-1;q++){ win(N-1,q,lab,&l,&r); addc(lab[q],l,r);} }
  size_t sz=(size_t)1<<N;
  i128 *g=calloc(sz,sizeof(i128)), *gs=calloc(sz,sizeof(i128));
  g[0]=1; gs[0]=1;
  for(uint32_t S=0;S<full;S++){ i128 c=g[S]; if(!c)continue; i128 cs=gs[S];
    for(int m=1;m<=N;m++){ uint32_t b=1u<<(m-1); if(S&b)continue; if(!ok(S,m))continue;
      g[S|b]+=c; if(__builtin_popcount(S>>m)&1) gs[S|b]-=cs; else gs[S|b]+=cs; } }
  printf("N %d mode %s\ntotal ",N,mode); pr(g[full]); printf("\nsigned "); pr(gs[full]); printf("\n");
  static i128 T[40],DE[40],MV[40],pos[40][40]; static long Rc[40],DEc[40],Ac[40];
  for(uint32_t S=0;;S++){ i128 c=g[S]; if(c){ int k=__builtin_popcount(S); T[k]+=c; Rc[k]++;
      i128 h=g[full&~S]; if(h)Ac[k]++; int v=0;
      for(int m=1;m<=N;m++){ uint32_t b=1u<<(m-1); if(S&b)continue; if(!ok(S,m))continue; v++;
        i128 h2=g[full&~(S|b)]; pos[m][k+1]+=c*h2; }
      if(v==0&&S!=full){DE[k]+=c;DEc[k]++;}
      MV[k]+=c*h*v; }
    if(S==full)break; }
  printf("T"); for(int k=0;k<=N;k++){printf(" ");pr(T[k]);} printf("\n");
  printf("reach"); for(int k=0;k<=N;k++)printf(" %ld",Rc[k]); printf("\n");
  printf("alive"); for(int k=0;k<=N;k++)printf(" %ld",Ac[k]); printf("\n");
  printf("deadsets"); for(int k=0;k<=N;k++)printf(" %ld",DEc[k]); printf("\n");
  printf("deadprefixes"); for(int k=0;k<=N;k++){printf(" ");pr(DE[k]);} printf("\n");
  printf("moves"); for(int k=0;k<N;k++){printf(" ");pr(MV[k]);} printf("\n");
  for(int m=1;m<=N;m++){ printf("pos %d",m); for(int k=1;k<=N;k++){printf(" ");pr(pos[m][k]);} printf("\n"); }
  return 0;
}

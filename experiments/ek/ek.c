/* ek.c: Conjecture E_k.  For every k-subset D of [lo, N+1-lo] (default lo = 2: avoiding the end
   panels 1 and N), decide whether D is co-reachable: whether the free panels can be placed one
   by one on the background D, every step valid (|placed n L(m)| = |placed n R(m)|).
   Order: Theorem G (some centre), then DFS witnesses with the centre-distance order for several
   centres, then an exhaustive DFS with memo (certifies dead, or reports unresolved).
   Only sets with D <= mirror(D) (as sorted tuples, reversed comparison) are examined; each
   reported set is listed with its mirror.
   Usage: ek N k [lo] [exhaustive-node-limit]
   Output: one line per N,k with counts, and every dead / unresolved set.  1 core, N <= 120. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static int N, K, LO;
static u128 L[130], R[130], FULL;
static inline int pc(u128 x){return __builtin_popcountll((uint64_t)x)+__builtin_popcountll((uint64_t)(x>>64));}
static inline int imb(u128 S,int m){return pc(S&L[m])-pc(S&R[m]);}
static inline int has(u128 S,int m){return (int)((S>>(m-1))&1);}
static inline u128 bit(int m){return ((u128)1)<<(m-1);}
#define HB 22
static u128 *ht; static uint32_t *hst; static uint32_t stamp=1; static size_t hmask; static long nodes, limit; static int aborted;
static size_t hh(u128 s){uint64_t a=(uint64_t)s,b=(uint64_t)(s>>64);return ((a*0x9E3779B97F4A7C15ull)^(b*0xC2B2AE3D27D4EB4Full))>>(64-HB);}
static long hcount;
static int hfind(u128 s){size_t h=hh(s);while(hst[h]==stamp){if(ht[h]==s)return 1;h=(h+1)&hmask;}return 0;}
static void hins(u128 s){if(hcount>(long)(hmask*3/4))return; size_t h=hh(s);while(hst[h]==stamp){if(ht[h]==s)return;h=(h+1)&hmask;}ht[h]=s;hst[h]=stamp;hcount++;}
static int ord[130];
static int inwardG(u128 B);
static int dfs(u128 S){
  if(S==FULL||inwardG(S))return 1;   /* Theorem G completes from S */
  if(++nodes>limit){aborted=1;return 0;}
  if(hfind(S))return 0;
  for(int i=0;i<N;i++){int m=ord[i]; if(has(S,m))continue; if(imb(S,m)==0){ if(dfs(S|bit(m)))return 1; if(aborted)return 0;}}
  hins(S);return 0;
}
static void setord(int c2){ /* order by |2m - c2| */
  for(int i=0;i<N;i++)ord[i]=i+1;
  for(int i=1;i<N;i++){int x=ord[i],dx=abs(2*x-c2),j=i-1;while(j>=0&&abs(2*ord[j]-c2)>dx){ord[j+1]=ord[j];j--;}ord[j+1]=x;}
}
static void hclear(void){stamp++;hcount=0;}
/* Local relaxation (sound dead certificate): core = free panels of [1, w] (w <= (N+1)/2, so
   every core window is [1, 2m-1] inside [1, W], W = 2w - 1); the free panels of [w+1, W] are
   wildcards that may be placed at any time; panels beyond W are ignored.  If no relaxed play
   places all the core, D is dead.  Returns 1 if dead. */
static uint8_t *vis; static uint32_t *stk;
static int localdead(u128 B,int w){
  int W=2*w-1; if(W>N||2*w>N+1||W>25)return 0;
  uint32_t full=((1u<<W)-1), base=(uint32_t)B&full, core=0;
  for(int m=1;m<=w;m++)if(!((base>>(m-1))&1))core|=1u<<(m-1);
  if(!core)return 0;
  memset(vis,0,((size_t)1<<W)/8+1);
  long sp=0; stk[sp++]=base; vis[base>>3]|=1<<(base&7);
  while(sp){ uint32_t p=stk[--sp]; if((p&core)==core)return 0;
    for(int x=1;x<=W;x++){ if((p>>(x-1))&1)continue; int ok=1;
      if(x<=w){ uint32_t Lm=((1u<<(x-1))-1), Rm=(((1u<<(2*x-1))-1)&~((1u<<x)-1)); ok=__builtin_popcount(p&Lm)==__builtin_popcount(p&Rm);}
      if(!ok)continue; uint32_t q=p|(1u<<(x-1)); if(vis[q>>3]&(1<<(q&7)))continue; vis[q>>3]|=1<<(q&7); stk[sp++]=q; }
  }
  return 1;
}
static u128 mirrorset(u128 B){u128 M=0;for(int m=1;m<=N;m++)if(has(B,m))M|=bit(N+1-m);return M;}
static int lastw, lastside;
static uint64_t rng=88172645463325252ull; static uint64_t xr(void){rng^=rng<<13;rng^=rng>>7;rng^=rng<<17;return rng;}
static void setordr(int c2,int R){ int key[130];
  for(int i=0;i<N;i++){ord[i]=i+1;key[i+1]=abs(2*(i+1)-c2)+(R?(int)(xr()%R):0);}
  for(int i=1;i<N;i++){int x=ord[i],j=i-1;while(j>=0&&key[ord[j]]>key[x]){ord[j+1]=ord[j];j--;}ord[j+1]=x;}
}
/* 0 = unresolved, 1 = witness, 2 = dead (exhaustive), 3 = dead (local, radius lastw) */
static long wlimit=20000; static int nrand=60;
static int decide(u128 B,long exlimit){
  int cs[8]={N+1,2,2*N,(N+1)/2,3*(N+1)/2,N+1-(N+1)/3,N+1+(N+1)/3,N};
  for(int t=0;t<8;t++){ setord(cs[t]); hclear(); nodes=0; limit=wlimit; aborted=0; if(dfs(B))return 1; }
  u128 M=mirrorset(B);
  for(int w=3;w<=13;w++){ if(localdead(B,w)){lastw=w;lastside=0;return 3;} if(localdead(M,w)){lastw=w;lastside=1;return 3;} }
  for(int t=0;t<nrand;t++){ int c2=2+(int)(xr()%(2*N-1)); int R=(t%3==0)?0:(t%3==1?4:12);
    setordr(c2,R); hclear(); nodes=0; limit=wlimit; aborted=0; if(dfs(B))return 1; }
  setord(N+1); hclear(); nodes=0; limit=exlimit; aborted=0;
  if(dfs(B))return 1;
  return aborted?0:2;
}
static int inwardG(u128 B){ int maxneg=0,minpos=N+1;
  for(int m=1;m<=N;m++){ if(has(B,m))continue; int I=imb(B,m); if(I<0&&m>maxneg)maxneg=m; if(I>0&&m<minpos)minpos=m;}
  return maxneg<minpos; }
static long nset,nG,ndead,nunres; static int cur[10]; static long exlim;
static void report(const char*tag){ printf("  %s N=%d:",tag,N); for(int i=0;i<K;i++)printf(" %d",cur[i]); printf("   (mirror"); for(int i=K-1;i>=0;i--)printf(" %d",N+1-cur[i]); printf(")\n"); fflush(stdout);}
static void enumsets(u128 S,int start,int depth){
  if(depth==K){
    /* canonical under mirror: compare sorted tuple with sorted mirror tuple */
    int mir[10]; for(int i=0;i<K;i++)mir[i]=N+1-cur[K-1-i];
    int c=0; for(int i=0;i<K;i++){ if(cur[i]!=mir[i]){c=(cur[i]<mir[i])?-1:1;break;} }
    if(c>0)return;
    nset++; if(inwardG(S)){nG++;return;}
    int r=decide(S,exlim);
    if(r==2){ndead++;report("DEAD");} else if(r==3){ndead++;char t[40];sprintf(t,"DEAD-LOCAL%c%d",lastside?'R':'L',lastw);report(t);} else if(r==0){nunres++;report("UNRESOLVED");}
    return;}
  for(int m=start;m<=N+1-LO;m++){cur[depth]=m;enumsets(S|bit(m),m+1,depth+1);}
}
int main(int argc,char**argv){
  N=atoi(argv[1]); K=atoi(argv[2]); LO=argc>3?atoi(argv[3]):2; exlim=argc>4?atol(argv[4]):20000000L;
  if(argc>5)wlimit=atol(argv[5]);
  FULL=0; for(int m=1;m<=N;m++)FULL|=bit(m);
  for(int m=1;m<=N;m++){int r=m-1<N-m?m-1:N-m;L[m]=R[m]=0;for(int d=1;d<=r;d++){L[m]|=bit(m-d);R[m]|=bit(m+d);}}
  vis=malloc(((size_t)1<<25)/8+8); stk=malloc(sizeof(uint32_t)<<25);
  if(argc>6)nrand=atoi(argv[6]);
  ht=malloc(sizeof(u128)<<HB); hst=calloc((size_t)1<<HB,4); hmask=(1ull<<HB)-1;
  if(argc>2&&!strcmp(argv[2],"set")){ /* ek N set x1 x2 ... : decide one set */
    u128 B=0; K=0; for(int i=3;i<argc;i++){cur[K++]=atoi(argv[i]);B|=bit(atoi(argv[i]));}
    exlim=20000000L; int r=inwardG(B)?1:decide(B,exlim);
    if(r==1)report("LIVE"); else if(r==2)report("DEAD"); else if(r==3){char t[40];sprintf(t,"DEAD-LOCAL%c%d",lastside?'R':'L',lastw);report(t);} else report("UNRESOLVED");
    return 0; }
  nset=nG=ndead=nunres=0; enumsets(0,LO,0);
  printf("N=%d k=%d lo=%d: sets(up to mirror)=%ld G=%ld dead=%ld unresolved=%ld\n",N,K,LO,nset,nG,ndead,nunres);
  return 0;
}

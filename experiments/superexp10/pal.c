// pal.c: palindromic chains x, t0, rev(sig x) for odd q (search for x).
// usage: ./pal q nu [mode] [budget] [a] [c]  (middle block M = an ordering of {t0, a, sig a, c, sig c})
//   mode 0: free transversal; mode 1: allowed elements read from stdin.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef unsigned __int128 u128;
int q, nu, k, t0, ma = 0, mb = 0, kk, mc = 0, md2 = 0, nm = 0;
int mel[8], mbest[8];
int midord[6][3];
int sg[260];
int allowed[260];
long long nodes, budget;
int xs[260];
static inline int sigf(int t){ return ((nu - t) % q + q) % q + 1; }
static inline int cnt(u128 S, int lo, int hi){ // count S in [lo,hi], 1-based bits
  if (lo > hi) return 0;
  int len = hi - lo + 1;
  u128 m = (len >= 128) ? (~(u128)0) : (((u128)1 << len) - 1);
  m <<= lo;
  u128 v = S & m;
  return __builtin_popcountll((uint64_t)v) + __builtin_popcountll((uint64_t)(v >> 64));
}
static inline int stepok(u128 S, int t){
  int R = t - 1 < q - t ? t - 1 : q - t;
  return cnt(S, t - R, t - 1) == cnt(S, t + 1, t + R);
}
#define HS (1<<22)
u128 *hk; unsigned char *hu;
static inline uint64_t hh(u128 x){ uint64_t a=(uint64_t)x, b=(uint64_t)(x>>64); a ^= b*0x9E3779B97F4A7C15ULL; a ^= a>>29; a*=0xBF58476D1CE4E5B9ULL; a^=a>>32; return a; }
int isdead(u128 S){ uint64_t h=hh(S)&(HS-1); while(hu[h]){ if(hk[h]==S) return 1; h=(h+1)&(HS-1);} return 0;}
long long nd=0;
void adddead(u128 S){ if(nd > HS*0.7) return; uint64_t h=hh(S)&(HS-1); while(hu[h]){ if(hk[h]==S) return; h=(h+1)&(HS-1);} hu[h]=1; hk[h]=S; nd++; }
int dfs(int d, u128 S, u128 T){
  if (d == kk) {
    
    // try every ordering of the middle set mel[0..nm-1] (Heap's algorithm over indices)
    int perm[8], c[8];
    for (int z = 0; z < nm; z++) { perm[z] = mel[z]; c[z] = 0; }
    for (int it = 0;; ) {
      u128 A = S, B = T; int ok = 1;
      for (int z = 0; z < nm && ok; z++) {
        int e = perm[z];
        if (!stepok(A, e) || !stepok(B, sg[e])) ok = 0;
        A |= (u128)1 << e; B |= (u128)1 << sg[e];
      }
      if (ok) { for (int z = 0; z < nm; z++) mbest[z] = perm[z]; return 1; }
      while (it < nm && c[it] >= it) { c[it] = 0; it++; }
      if (it >= nm) break;
      int sw = (it % 2 == 0) ? 0 : c[it];
      int tmp = perm[sw]; perm[sw] = perm[it]; perm[it] = tmp;
      c[it]++; it = 0;
    }
    return 0;
  }
  if (++nodes > budget) return 0;
  if (isdead(S)) return 0;
  for (int t = 1; t <= q; t++) {
    if (!allowed[t] || t == t0 || t == ma || t == mb || t == mc || t == md2) continue;
    if ((S >> t) & 1) continue;
    int u = sg[t];
    if ((S >> u) & 1) continue;
    if (!stepok(S, t) || !stepok(T, u)) continue;
    xs[d] = t;
    if (dfs(d + 1, S | ((u128)1 << t), T | ((u128)1 << u))) return 1;
    if (nodes > budget) return 0;
  }
  adddead(S);
  return 0;
}
int main(int argc, char **argv){
  q = atoi(argv[1]); nu = atoi(argv[2]);
  int mode = argc > 3 ? atoi(argv[3]) : 0;
  budget = argc > 4 ? atoll(argv[4]) : 20000000;
  k = (q - 1) / 2;
  ma = argc > 5 ? atoi(argv[5]) : 0;
  mc = argc > 6 ? atoi(argv[6]) : 0;
  for (int t = 1; t <= q; t++) { sg[t] = sigf(t); if (sg[t] == t) t0 = t; }
  for (int t = 1; t <= q; t++) allowed[t] = 1;
  if (mode > 0) {
    for (int t = 1; t <= q; t++) allowed[t] = 0;
    int v; while (scanf("%d", &v) == 1) allowed[v] = 1;
  }
  if (ma) mb = sg[ma];
  if (mc) md2 = sg[mc];
  kk = k - (ma ? 1 : 0) - (mc ? 1 : 0);
  mel[nm++] = t0; if (ma) { mel[nm++] = ma; mel[nm++] = mb; } if (mc) { mel[nm++] = mc; mel[nm++] = md2; }
  hk = malloc(sizeof(u128) * HS); hu = calloc(HS, 1);
  int r = dfs(0, 0, 0);
  printf("q=%d nu=%d t0=%d res=%s nodes=%lld", q, nu, t0, r ? "OK" : (nodes > budget ? "BUDGET" : "NONE"), nodes);
  if (r) { printf(" x="); for (int i = 0; i < kk; i++) printf("%d%s", xs[i], i + 1 < kk ? "," : "");
    printf(" M="); for (int z = 0; z < nm; z++) printf("%d%s", mbest[z], z + 1 < nm ? "," : ""); }
  printf("\n");
  return 0;
}

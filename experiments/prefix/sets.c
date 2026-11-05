/* sets.c: V(N,k) = number of k-subsets S of [1..N] with g(S) > 0 (S can be built by
 * valid steps in some order), and G(N,k) = sum over k-subsets of g(S) (= T(N,k), as a check).
 * usage: sets K Nmin Nmax
 * Enumerates combinations x1<...<xj recursively; for the current combination it keeps
 * g over all subsets (bitmasks), extending it with the 2^(j-1) new masks when x_j is added.
 * Output: N V(N,1..K) | G(N,1..K) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long u64;
static int N, K, X[16];
static u64 g[1 << 12];
static u64 V[16], G[16];

/* is adding X[i] to the set {X[t] : t in mask} a valid step? */
static int valid(int mask, int i){
  int m = X[i], L = 0, R = 0;
  if (m - 1 <= N - m){ int hi = 2*m - 1;
    for (int t = 0; mask >> t; t++) if (mask >> t & 1){ int x = X[t]; if (x < m) L++; else if (x <= hi) R++; } }
  else { int lo = 2*m - N;
    for (int t = 0; mask >> t; t++) if (mask >> t & 1){ int x = X[t]; if (x > m) R++; else if (x >= lo) L++; } }
  return L == R;
}
static void rec(int j, int start){ /* j elements chosen */
  if (j == K) return;
  for (int x = start; x <= N; x++){
    X[j] = x; int bit = 1 << j;
    for (int sub = 0; sub < bit; sub++){ int mask = sub | bit; u64 s = 0;
      for (int i = 0; i <= j; i++) if (mask >> i & 1){ int pm = mask ^ (1 << i);
        if (g[pm] && valid(pm, i)) s += g[pm]; }
      g[mask] = s; }
    u64 v = g[(bit << 1) - 1];
    if (v){ V[j+1]++; G[j+1] += v; }
    rec(j + 1, x + 1);
  }
}
int main(int argc, char **argv){
  K = atoi(argv[1]); int a = atoi(argv[2]), b = atoi(argv[3]);
  for (N = a; N <= b; N++){
    memset(V, 0, sizeof V); memset(G, 0, sizeof G); g[0] = 1;
    rec(0, 1);
    printf("%d", N); for (int k = 1; k <= K; k++) printf(" %llu", V[k]);
    printf(" |"); for (int k = 1; k <= K; k++) printf(" %llu", G[k]); printf("\n"); fflush(stdout);
  }
}

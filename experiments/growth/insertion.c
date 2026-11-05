/* insertion.c -- checks for the insertion-order upper bound (PROOFS.txt, section 2).
 *
 *   usage: ./insertion N        (exact L(N) by subset DP; N <= 26)
 *          ./insertion N max    (also enumerate all left-valid orders, N <= 12, and
 *                                compute max_t prod_m max(e_m, f_m)/(2m-1))
 *
 * L(N) = number of orderings of 1..N satisfying the constraints of the left-half panels
 * only (m <= (N+1)/2, window [1, 2m-1]).  a(N) <= L(N).
 * Theorem (PROOFS.txt): L(N) <= N! * max_t prod_{m=2}^{n1} max(e_m, f_m)/(2m-1)
 *                              <= N! * exp(-(n1 - 1)/16),  n1 = floor((N+1)/2),
 * where e_m (f_m) = number of panels of W_m \ {m} placed before (after) m.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>

static int N, n1;
static uint64_t Lm[64], Rm[64];
static double best; static long long leaves;

static void dfs(uint64_t S, int k, double prod) {
  if (k == N) { leaves++; if (prod > best) best = prod; return; }
  for (int m = 1; m <= N; m++) {
    uint64_t b = 1ULL << (m - 1);
    if (S & b) continue;
    double p = prod;
    if (m >= 2 && m <= n1) {
      int l = __builtin_popcountll(S & Lm[m]), r = __builtin_popcountll(S & Rm[m]);
      if (l != r) continue;
      int e = 2 * l, f = 2 * m - 2 - e;
      p *= (double)(e > f ? e : f) / (2 * m - 1);
    }
    dfs(S | b, k + 1, p);
  }
}

int main(int argc, char **argv) {
  N = atoi(argv[1]); n1 = (N + 1) / 2;
  for (int m = 1; m <= n1; m++) {
    Lm[m] = Rm[m] = 0;
    for (int d = 1; d <= m - 1; d++) { Lm[m] |= 1ULL << (m - d - 1); Rm[m] |= 1ULL << (m + d - 1); }
  }
  uint64_t NS = 1ULL << N, full = NS - 1;
  double *g = calloc(NS, sizeof(double));
  g[0] = 1;
  for (uint64_t S = 0; S < full; S++) {
    if (g[S] == 0) continue;
    for (int m = 1; m <= N; m++) {
      uint64_t b = 1ULL << (m - 1);
      if (S & b) continue;
      if (m >= 2 && m <= n1 && __builtin_popcountll(S & Lm[m]) != __builtin_popcountll(S & Rm[m])) continue;
      g[S | b] += g[S];
    }
  }
  double lf = lgamma(N + 1.0), L = g[full];
  printf("N=%d L(N)=%.0f logL=%.4f logN!=%.4f logL/logN!=%.4f  log(L/N!)=%.4f  bound -(n1-1)/16=%.4f\n",
         N, L, log(L), lf, log(L) / lf, log(L) - lf, -(n1 - 1) / 16.0);
  if (argc > 2) {
    best = 0; leaves = 0; dfs(0, 0, 1.0);
    printf("   enumerated %lld left-valid orders; log max prod = %.4f (>= log(L/N!) = %.4f, <= %.4f)\n",
           leaves, log(best), log(L) - lf, -(n1 - 1) / 16.0);
  }
  return 0;
}

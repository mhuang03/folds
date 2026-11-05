/* interleave.c -- interleavings of an even-class sequence and an odd-class sequence.
 *
 *   usage: ./interleave N
 *
 * For every pair (sigma, tau) of valid sequences of the half problems (sizes floor(N/2)
 * for the evens, ceil(N/2) for the odds), counts the interleavings of 2*sigma and
 * 2*tau-1 that are valid for N (lattice-path DP).  Prints the distribution summary and
 * the best pair.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static uint64_t Lm[64], Rm[64];
static int N;
static int valid(uint64_t S, int m, int n, uint64_t *L, uint64_t *R) {
  (void)n; return __builtin_popcountll(S & L[m]) == __builtin_popcountll(S & R[m]);
}
static void mk(int n, uint64_t *L, uint64_t *R) {
  for (int m = 1; m <= n; m++) {
    int D = m - 1 < n - m ? m - 1 : n - m;
    L[m] = R[m] = 0;
    for (int d = 1; d <= D; d++) { L[m] |= 1ULL << (m - d - 1); R[m] |= 1ULL << (m + d - 1); }
  }
}
static int *list; static long cnt; static int cur[64];
static uint64_t Ls[64], Rs[64];
static void dfs(int n, int k, uint64_t S) {
  if (k == n) { memcpy(list + cnt * n, cur, n * sizeof(int)); cnt++; return; }
  for (int m = 1; m <= n; m++) {
    uint64_t b = 1ULL << (m - 1);
    if (S & b) continue;
    if (!valid(S, m, n, Ls, Rs)) continue;
    cur[k] = m; dfs(n, k + 1, S | b);
  }
}
static long enumerate(int n, int **out) {
  long cap = 1; for (int i = 2; i <= n; i++) cap *= i;  /* crude bound */
  if (cap > 30000000) cap = 30000000;
  list = malloc(cap * n * sizeof(int)); cnt = 0;
  mk(n, Ls, Rs); dfs(n, 0, 0); *out = list; return cnt;
}
int main(int argc, char **argv) {
  N = atoi(argv[1]);
  int nE = N / 2, nO = (N + 1) / 2;
  mk(N, Lm, Rm);
  int *E, *O; long cE = enumerate(nE, &E), cO = enumerate(nO, &O);
  /* precompute prefix masks */
  uint64_t *PE = malloc(cE * (nE + 1) * sizeof(uint64_t)), *PO = malloc(cO * (nO + 1) * sizeof(uint64_t));
  for (long i = 0; i < cE; i++) { uint64_t S = 0; PE[i * (nE + 1)] = 0;
    for (int k = 0; k < nE; k++) { S |= 1ULL << (2 * E[i * nE + k] - 1); PE[i * (nE + 1) + k + 1] = S; } }
  for (long i = 0; i < cO; i++) { uint64_t S = 0; PO[i * (nO + 1)] = 0;
    for (int k = 0; k < nO; k++) { S |= 1ULL << (2 * O[i * nO + k] - 2); PO[i * (nO + 1) + k + 1] = S; } }
  double total = 0, best = 0; long bi = 0, bj = 0; long hist[64] = {0};
  double dp[64][64];
  for (long i = 0; i < cE; i++) for (long j = 0; j < cO; j++) {
    for (int a = 0; a <= nE; a++) for (int b = 0; b <= nO; b++) {
      double v = (a == 0 && b == 0) ? 1 : 0;
      uint64_t S;
      if (a > 0) { S = PE[i * (nE + 1) + a - 1] | PO[j * (nO + 1) + b]; int m = 2 * E[i * nE + a - 1];
        if (valid(S, m, N, Lm, Rm)) v += dp[a - 1][b]; }
      if (b > 0) { S = PE[i * (nE + 1) + a] | PO[j * (nO + 1) + b - 1]; int m = 2 * O[j * nO + b - 1] - 1;
        if (valid(S, m, N, Lm, Rm)) v += dp[a][b - 1]; }
      dp[a][b] = v;
    }
    double I = dp[nE][nO]; total += I;
    int lg = 0; double t = I; while (t >= 2) { t /= 2; lg++; } hist[lg]++;
    if (I > best) { best = I; bi = i; bj = j; }
  }
  printf("N=%d pairs=%ld*%ld total_interleavings=%.0f avg=%.3f max=%.0f\n", N, cE, cO, total, total / (cE * (double)cO), best);
  printf(" log2 histogram:"); for (int k = 0; k < 64; k++) if (hist[k]) printf(" %d:%ld", k, hist[k]); printf("\n");
  printf(" best sigma (evens):"); for (int k = 0; k < nE; k++) printf(" %d", 2 * E[bi * nE + k]);
  printf("\n best tau (odds):"); for (int k = 0; k < nO; k++) printf(" %d", 2 * O[bj * nO + k] - 1); printf("\n");
  return 0;
}

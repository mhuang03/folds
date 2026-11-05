/* classes.c -- g(S) (orderings that build S) and h(S) (completions of S) for structured S.
 *
 *   usage: ./classes N
 *
 * For every modulus q = 2..6 and every union of residue classes mod q (as a set of
 * panels 1..N), prints g(S), h(S) and g(S)*h(S)/a(N) when g(S) h(S) > 0.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int main(int argc, char **argv) {
  int N = atoi(argv[1]);
  uint64_t full = (1ULL << N) - 1, NS = 1ULL << N;
  uint64_t Lm[64], Rm[64];
  for (int m = 1; m <= N; m++) {
    int D = m - 1 < N - m ? m - 1 : N - m;
    Lm[m] = Rm[m] = 0;
    for (int d = 1; d <= D; d++) { Lm[m] |= 1ULL << (m - d - 1); Rm[m] |= 1ULL << (m + d - 1); }
  }
  double *g = calloc(NS, sizeof(double)), *h = calloc(NS, sizeof(double));
  g[0] = 1;
  for (uint64_t S = 0; S < full; S++) {
    if (g[S] == 0) continue;
    for (int m = 1; m <= N; m++) {
      uint64_t b = 1ULL << (m - 1);
      if (S & b) continue;
      if (__builtin_popcountll(S & Lm[m]) == __builtin_popcountll(S & Rm[m])) g[S | b] += g[S];
    }
  }
  h[full] = 1;
  for (uint64_t S = full; S-- > 0;) {
    double s = 0;
    for (int m = 1; m <= N; m++) {
      uint64_t b = 1ULL << (m - 1);
      if (S & b) continue;
      if (__builtin_popcountll(S & Lm[m]) == __builtin_popcountll(S & Rm[m])) s += h[S | b];
    }
    h[S] = s;
  }
  double a = h[0];
  printf("N=%d a=%.0f\n", N, a);
  for (int q = 2; q <= 6; q++) {
    for (int u = 1; u < (1 << q) - 1; u++) {
      uint64_t S = 0;
      for (int m = 1; m <= N; m++) if ((u >> (m % q)) & 1) S |= 1ULL << (m - 1);
      if (g[S] * h[S] > 0) {
        printf("q=%d classes=", q);
        for (int i = 0; i < q; i++) if ((u >> i) & 1) printf("%d", i);
        printf("  |S|=%d g=%.0f h=%.0f share=%.3g\n", __builtin_popcountll(S), g[S], h[S], g[S] * h[S] / a);
      }
    }
  }
  return 0;
}

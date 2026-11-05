/* splits.c -- "splits" of the strip: sets A such that A (complete) is balanced at every
 * panel outside A and the complement B is balanced at every panel of A.
 *
 *   usage: ./splits N
 *
 * For each split A, compares g(A) (orderings building A) with a(|A|) and h(A)
 * (completions) with a(N-|A|).  Prints the number of splits by |A| and the total
 * sum over splits of g(A) h(A) (a lower bound for a(N), the families being disjoint).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int main(int argc, char **argv) {
  int N = atoi(argv[1]);
  int verbose = argc > 2;
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
  /* a(n) for n < N: read from the counts file if available, else compute small ones */
  static double A[64];
  FILE *f = fopen("../semi_counts.txt", "r");
  if (f) { int n; double v; char line[256];
    while (fgets(line, sizeof line, f)) if (sscanf(line, "%d %lf", &n, &v) == 2 && n < 64) A[n] = v;
    fclose(f); }
  A[0] = 1;
  long cnt[64] = {0}; double sum = 0; long nsplit = 0, good = 0;
  for (uint64_t S = 1; S < full; S++) {
    uint64_t B = full & ~S; int ok = 1;
    for (int m = 1; m <= N && ok; m++) {
      uint64_t b = 1ULL << (m - 1);
      uint64_t T = (S & b) ? B : S;
      if (__builtin_popcountll(T & Lm[m]) != __builtin_popcountll(T & Rm[m])) ok = 0;
    }
    if (!ok) continue;
    int k = __builtin_popcountll(S);
    nsplit++; cnt[k]++; sum += g[S] * h[S];
    int isgood = (g[S] == A[k] && h[S] == A[N - k]);
    good += isgood;
    if (verbose) {
      for (int m = 1; m <= N; m++) putchar((S >> (m - 1)) & 1 ? '#' : '.');
      printf("  k=%2d g=%.0f a(k)=%.0f h=%.0f a(N-k)=%.0f %s\n", k, g[S], A[k], h[S], A[N - k], isgood ? "" : "MISMATCH");
    }
  }
  printf("N=%d a=%.0f splits=%ld (g=a(k),h=a(N-k) for %ld)  sum g*h=%.0f share=%.4f  by k:", N, h[0], nsplit, good, sum, sum / h[0]);
  for (int k = 0; k <= N; k++) if (cnt[k]) printf(" %d:%ld", k, cnt[k]);
  printf("\n");
  return 0;
}

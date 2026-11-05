/* choices.c -- branching statistics of the fold-sequence tree, by a DP over all subsets.
 *
 *   usage: ./choices N
 *
 * g(S)  = number of valid orderings building S (forward),
 * h(S)  = number of valid completions of S (backward), live(S) <=> h(S) > 0,
 * V(S)  = number of valid next panels m (step (S,m) valid),
 * D(S)  = number of valid next panels with S+m live (= out-degree in the pruned tree).
 *
 * Prints, per k = |S|:
 *   maxV   = max V(S) over reachable S of size k         (and maxV/(N-k))
 *   maxD   = max D(S) over reachable live S of size k
 *   avgD   = average of D(S_k) along a uniformly random valid sequence
 *   geoD   = exp E[log D(S_k)] along a uniformly random valid sequence
 *   Hk     = entropy of the k-th step given S_k (uniform valid sequence)
 * and globally
 *   logM   = log of max over valid sequences of prod_k D(S_k)  (tree bound: a(N) <= M)
 *   logMV  = log of max over valid sequences of prod_k V(S_k)
 *   log a(N), log N!.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>

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
  float *M = calloc(NS, sizeof(float)), *MV = calloc(NS, sizeof(float));
  /* valid-move mask cache is too big for N=24 x 4 bytes? 64MB: fine */
  uint32_t *vm = malloc(NS * sizeof(uint32_t));
  for (uint64_t S = 0; S < NS; S++) {
    uint32_t v = 0;
    for (int m = 1; m <= N; m++) {
      uint64_t b = 1ULL << (m - 1);
      if (S & b) continue;
      if (__builtin_popcountll(S & Lm[m]) == __builtin_popcountll(S & Rm[m])) v |= (uint32_t)b;
    }
    vm[S] = v;
  }
  g[0] = 1;
  for (uint64_t S = 0; S < full; S++) {
    if (g[S] == 0) continue;
    uint32_t v = vm[S];
    while (v) { int i = __builtin_ctz(v); v &= v - 1; g[S | (1ULL << i)] += g[S]; }
  }
  h[full] = 1; M[full] = 0; MV[full] = 0;
  for (uint64_t S = full; S-- > 0;) {
    uint32_t v = vm[S]; double s = 0; int deg = 0; float best = -1, bestv = -1;
    while (v) {
      int i = __builtin_ctz(v); v &= v - 1;
      uint64_t T = S | (1ULL << i);
      if (h[T] > 0) { s += h[T]; deg++; if (M[T] > best) best = M[T]; if (MV[T] > bestv) bestv = MV[T]; }
    }
    h[S] = s;
    if (deg) {
      M[S] = best + logf((float)deg);
      MV[S] = bestv + logf((float)__builtin_popcount(vm[S]));
    }
  }
  double a = h[0];
  int maxV[64] = {0}, maxD[64] = {0};
  double sumD[64] = {0}, sumlogD[64] = {0}, H[64] = {0};
  uint64_t argV[64] = {0};
  for (uint64_t S = 0; S < full; S++) {
    if (g[S] == 0) continue;
    int k = __builtin_popcountll(S);
    int V = __builtin_popcount(vm[S]);
    if (V > maxV[k]) { maxV[k] = V; argV[k] = S; }
    if (h[S] == 0) continue;
    double w = g[S] * h[S] / a; /* prob that a uniform valid seq passes S */
    int deg = 0; double ent = 0;
    uint32_t v = vm[S];
    while (v) {
      int i = __builtin_ctz(v); v &= v - 1;
      uint64_t T = S | (1ULL << i);
      if (h[T] > 0) { deg++; double p = h[T] / h[S]; ent -= p * log(p); }
    }
    if (deg > maxD[k]) maxD[k] = deg;
    sumD[k] += w * deg; sumlogD[k] += w * log(deg); H[k] += w * ent;
  }
  double lf = lgamma(N + 1.0);
  printf("N=%d a=%.0f loga=%.4f logN!=%.4f ratio=%.4f\n", N, a, log(a), lf, log(a) / lf);
  printf("logM(prod pruned degrees)=%.4f ratio=%.4f   logMV(prod valid counts)=%.4f ratio=%.4f\n",
         M[0], M[0] / lf, MV[0], MV[0] / lf);
  double sH = 0, sL = 0;
  printf(" k  N-k maxV maxV/(N-k) maxD   avgD    geoD     Hk   argmaxV\n");
  for (int k = 0; k < N; k++) {
    sH += H[k]; sL += sumlogD[k];
    printf("%2d %3d %4d %8.3f %5d %7.3f %7.3f %7.3f  ", k, N - k, maxV[k], (double)maxV[k] / (N - k),
           maxD[k], sumD[k], exp(sumlogD[k]), H[k]);
    for (int m = 1; m <= N; m++) putchar((argV[k] >> (m - 1)) & 1 ? '#' : '.');
    putchar('\n');
  }
  printf("sum H = %.4f (should equal log a = %.4f), sum E log D = %.4f\n", sH, log(a), sL);
  return 0;
}

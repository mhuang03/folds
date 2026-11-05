/* smc.c -- sequential Monte Carlo (population / "go with the winners") estimate of a(N)
 * for large N.  Not a proof; used to see the growth exponent beyond N = 33.
 *
 *   usage: ./smc N particles seed
 *
 * Each particle is a valid prefix S.  At step k every particle computes its number of
 * valid next panels V_i (O(N) via prefix sums and the prefix form of the condition).
 * The estimate is   a(N) ~ prod_k mean_i V_i ,
 * which is unbiased for the number of leaves at depth N of the tree of valid prefixes.
 * Particles are resampled proportionally to V_i and each moves to a uniformly random
 * valid child.  Also reports the mean fraction V/(N-k) and the mean max |discrepancy|
 * D = max_x |P(x) - s x / N| of the particle sets.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

int main(int argc, char **argv) {
  int N = atoi(argv[1]); int P = atoi(argv[2]); rs = argc > 3 ? strtoull(argv[3], 0, 10) * 2654435761ULL + 1 : 88172645463325252ULL;
  unsigned char *S = calloc((size_t)P * (N + 2), 1), *S2 = calloc((size_t)P * (N + 2), 1);
  int *V = malloc(P * sizeof(int)), *cum = malloc((N + 2) * sizeof(int));
  int *vl = malloc((size_t)P * N * sizeof(int));
  double logZ = 0;
  int step_print = N / 8 ? N / 8 : 1;
  for (int k = 0; k < N; k++) {
    double sum = 0, fr = 0, disc = 0;
    for (int i = 0; i < P; i++) {
      unsigned char *s = S + (size_t)i * (N + 2);
      cum[0] = 0;
      for (int x = 1; x <= N; x++) cum[x] = cum[x - 1] + s[x];
      int v = 0;
      for (int m = 1; m <= N; m++) {
        if (s[m]) continue;
        int r = m - 1 < N - m ? m - 1 : N - m;
        int L = cum[m - 1] - cum[m - 1 - r], R = cum[m + r] - cum[m];
        if (L == R) vl[(size_t)i * N + v++] = m;
      }
      V[i] = v; sum += v; fr += (double)v / (N - k);
      double d = 0;
      for (int x = 1; x <= N; x++) { double e = fabs(cum[x] - (double)k * x / N); if (e > d) d = e; }
      disc += d;
    }
    if (sum == 0) { printf("N=%d extinct at k=%d\n", N, k); return 0; }
    logZ += log(sum / P);
    if (k % step_print == 0) fprintf(stderr, "k=%d meanV=%.3f frac=%.3f disc=%.3f\n", k, sum / P, fr / P, disc / P);
    /* systematic resampling proportional to V */
    double u = urand() * sum / P, acc = 0; int j = 0;
    for (int i = 0; i < P; i++) {
      double target = u + i * sum / P;
      while (acc + V[j] <= target) { acc += V[j]; j++; }
      memcpy(S2 + (size_t)i * (N + 2), S + (size_t)j * (N + 2), N + 2);
      int m = vl[(size_t)j * N + (rnd() % V[j])];
      S2[(size_t)i * (N + 2) + m] = 1;
    }
    unsigned char *t = S; S = S2; S2 = t;
  }
  double lf = lgamma(N + 1.0);
  printf("N=%d P=%d loga_est=%.4f logN!=%.4f ratio=%.4f  loga/(NlogN)=%.4f\n", N, P, logZ, lf, logZ / lf, logZ / (N * log(N)));
  return 0;
}

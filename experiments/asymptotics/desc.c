/* desc.c -- uniform random descent ("random greedy"): at every step choose a uniformly random
 * valid panel.  No resampling, so a single path costs O(N^2) and N can be large (N <= 65535).
 *
 *   usage: ./desc N runs seed [statfile]
 *
 * For each run prints  N, completed?, k_end, H = sum_k log V_k  (the log of the inverse
 * probability of the path).  Importance-sampling identity: a(N) = E[ 1{complete} prod_k V_k ],
 * hence by Jensen  log a(N) >= log P(complete) + E[ H | complete ]  (a rigorous inequality for
 * the true expectations; here estimated by sampling).
 * statfile: at 64 checkpoints t = j/64, per run: frac = V/(N-k), sdJ (std of J over free
 * panels), Dmax = max|E|, and the octave decomposition of var(J) is not computed here
 * (see dyadic.py); instead the dyadic level variances of D are in levels.c.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }

int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: desc N runs seed [statfile]\n"); return 1; }
  int N = atoi(argv[1]), R = atoi(argv[2]);
  rs = (argc > 3 ? strtoull(argv[3], 0, 10) : 1) * 2654435761ULL + 88172645463325252ULL;
  for (int i = 0; i < 10; i++) rnd();
  FILE *sf = argc > 4 ? fopen(argv[4], "a") : NULL;
  uint16_t *F = malloc(2 * (N + 1)); int8_t *J = malloc(N + 1); int *Z = malloc(sizeof(int) * (N + 1));
  for (int run = 0; run < R; run++) {
    int f = N; for (int m = 0; m < N; m++) { F[m] = m + 1; J[m] = 0; }
    double H = 0; int k = 0, done = 1;
    for (k = 0; k < N; k++) {
      int v = 0;
      for (int m = 0; m < f; m++) if (J[m] == 0) Z[v++] = m;
      if (v == 0) { done = 0; break; }
      H += log((double)v);
      if (sf && k > 0 && (int)((long)k * 64 / N) != (int)((long)(k - 1) * 64 / N)) {
        double s1 = 0, s2 = 0, d = 0; int q = 0, cnt = 0;
        for (int m = 0; m < f; m++) { s1 += J[m]; s2 += (double)J[m] * J[m]; }
        for (int x = 1; x <= N; x++) {
          if (q < f && F[q] == x) q++; else cnt++;
          double e = fabs(cnt - (double)k * x / N); if (e > d) d = e;
        }
        fprintf(sf, "N=%d run=%d k=%d t=%.4f frac=%.5f sdJ=%.4f meanJ=%.4f Dmax=%.4f\n", N, run, k, (double)k / N,
                (double)v / f, sqrt(fmax(0, s2 / f - (s1 / f) * (s1 / f))), s1 / f, d);
      }
      int xi = Z[rnd() % v], x = F[xi], a = (x + 2) / 2, b = (N + x) / 2;
      for (int m = 0; m < xi; m++) J[m] += (F[m] >= a);
      for (int m = xi + 1; m < f; m++) { F[m - 1] = F[m]; J[m - 1] = J[m] - (F[m] <= b); }
      f--;
    }
    printf("N=%d run=%d complete=%d k_end=%d H=%.4f logN!=%.4f H/N=%.5f\n", N, run, done, k, H, lgamma(N + 1.0), H / N);
    fflush(stdout);
  }
  return 0;
}

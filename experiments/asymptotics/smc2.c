/* smc2.c -- sequential Monte Carlo estimate of a(N) with incremental "imbalance" field
 * and discrepancy diagnostics.  Not a proof.
 *
 *   usage: ./smc2 N particles seed [statfile]
 *
 * State of a particle: occupancy occ[1..N] and the imbalance field
 *     J(m) = #(S in right arm of m) - #(S in left arm of m),
 * so m is a valid next panel iff occ[m] = 0 and J(m) = 0.  Adding panel x changes J by the
 * "dipole"  +1 on [ceil((x+1)/2), x-1],  -1 on [x+1, floor((N+x)/2)]   (O(N), vectorised).
 * Estimator: log a(N) ~ sum_k log mean_i V_i (unbiased for a(N) itself), with systematic
 * resampling proportional to V_i and a uniform valid child.
 * Diagnostics at 64 checkpoints k = t N (t = j/64): mean fraction V/(N-k); means of
 *   Dmax = max_x |P(x) - k x / N|,  sdJ = std of J over free panels, madJ = mean |J| over
 *   free panels, p1 = share of free panels with |J| = 1, and the histogram of J over free
 *   panels (|J| <= 40).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <math.h>

static uint64_t rs;
static inline uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static inline double urand(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

#define HB 40
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: smc2 N P seed [statfile]\n"); return 1; }
  int N = atoi(argv[1]); int P = atoi(argv[2]);
  rs = (argc > 3 ? strtoull(argv[3], 0, 10) : 1) * 2654435761ULL + 88172645463325252ULL;
  for (int i = 0; i < 10; i++) rnd();
  FILE *sf = argc > 4 ? fopen(argv[4], "w") : NULL;
  size_t W = N + 2;
  int8_t *J = calloc((size_t)P * W, 1), *J2 = calloc((size_t)P * W, 1);
  uint8_t *O = calloc((size_t)P * W, 1), *O2 = calloc((size_t)P * W, 1);
  int *V = malloc(P * sizeof(int));
  double logZ = 0;
  int nck = 64;
  for (int k = 0; k < N; k++) {
    double sum = 0;
    for (int i = 0; i < P; i++) {
      const int8_t *j = J + i * W; const uint8_t *o = O + i * W;
      int v = 0;
      for (int m = 1; m <= N; m++) v += (j[m] == 0) & (o[m] == 0);
      V[i] = v; sum += v;
    }
    if (sum == 0) { printf("N=%d extinct at k=%d\n", N, k); return 0; }
    logZ += log(sum / P);
    /* checkpoint diagnostics */
    if (sf && k > 0 && (int)((long)k * nck / N) != (int)((long)(k - 1) * nck / N)) {
      double fr = 0, dm = 0, sd = 0, mad = 0, p1 = 0; double hist[2 * HB + 1] = {0};
      for (int i = 0; i < P; i++) {
        const int8_t *j = J + i * W; const uint8_t *o = O + i * W;
        int cnt = 0; double d = 0, s1 = 0, s2 = 0, a1 = 0; int q1 = 0;
        for (int x = 1; x <= N; x++) {
          cnt += o[x]; double e = fabs(cnt - (double)k * x / N); if (e > d) d = e;
          if (!o[x]) { int jj = j[x]; s1 += jj; s2 += (double)jj * jj; a1 += abs(jj); q1 += (abs(jj) == 1);
            if (jj >= -HB && jj <= HB) hist[jj + HB] += 1.0 / (N - k); }
        }
        double f = N - k;
        fr += V[i] / f; dm += d; sd += sqrt(fmax(0, s2 / f - (s1 / f) * (s1 / f))); mad += a1 / f; p1 += q1 / f;
      }
      fprintf(sf, "k=%d t=%.4f frac=%.5f Dmax=%.4f sdJ=%.4f madJ=%.4f p1=%.5f hist=", k, (double)k / N,
              fr / P, dm / P, sd / P, mad / P, p1 / P);
      for (int h = 0; h <= 2 * HB; h++) fprintf(sf, "%s%.5f", h ? "," : "", hist[h] / P);
      fprintf(sf, "\n"); fflush(sf);
    }
    /* systematic resampling proportional to V, then a uniform valid child */
    double step = sum / P, u = urand() * step, acc = 0; int jx = 0;
    for (int i = 0; i < P; i++) {
      double target = u + i * step;
      while (acc + V[jx] <= target) { acc += V[jx]; jx++; }
      int8_t *dj = J2 + i * W; uint8_t *dO = O2 + i * W;
      memcpy(dj, J + jx * W, W); memcpy(dO, O + jx * W, W);
      int r = rnd() % V[jx], x = 0;
      for (int m = 1; m <= N; m++) if (dj[m] == 0 && dO[m] == 0) { if (r-- == 0) { x = m; break; } }
      dO[x] = 1;
      int a = (x + 2) / 2, b = (N + x) / 2;  /* ceil((x+1)/2) = floor((x+2)/2) */
      for (int m = a; m < x; m++) dj[m]++;
      for (int m = x + 1; m <= b; m++) dj[m]--;
    }
    int8_t *t = J; J = J2; J2 = t; uint8_t *t2 = O; O = O2; O2 = t2;
  }
  double lf = lgamma(N + 1.0);
  printf("N=%d P=%d loga_est=%.4f logN!=%.4f ratio=%.5f deficit=%.5f\n", N, P, logZ, lf, logZ / lf, (lf - logZ) / N);
  return 0;
}

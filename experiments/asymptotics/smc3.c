/* smc3.c -- SMC estimate of a(N) with a compact free-panel representation and a growing
 * population near the end (where the prefix tree has its dead ends).  Not a proof.
 *
 *   usage: ./smc3 N P seed [Pmax] [statfile]
 *
 * A particle stores only its free panels (sorted) and the imbalance J on them:
 *   J(m) = #(S in right arm of m) - #(S in left arm of m);  m is a valid move iff J(m) = 0.
 * Adding x:  J += 1 on free m in [ceil((x+1)/2), x-1],  J -= 1 on free m in [x+1, floor((N+x)/2)].
 * Cost per particle and step is O(N - k), so the population can grow as the free set
 * shrinks at constant total cost: P_k = min(Pmax, P * N / (N - k)).  With a varying
 * population, prod_k mean_i V_i  is still an unbiased estimator of a(N) (standard SMC).
 * Prints log a estimate; with a statfile, the cumulative log estimate at 64 checkpoints.
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
  if (argc < 3) { fprintf(stderr, "usage: smc3 N P seed [Pmax] [statfile]\n"); return 1; }
  int N = atoi(argv[1]); long P0 = atol(argv[2]);
  rs = (argc > 3 ? strtoull(argv[3], 0, 10) : 1) * 2654435761ULL + 88172645463325252ULL;
  for (int i = 0; i < 10; i++) rnd();
  long Pmax = argc > 4 ? atol(argv[4]) : 64 * P0;
  FILE *sf = argc > 5 ? fopen(argv[5], "w") : NULL;
  size_t cap = (size_t)P0 * N + 16;               /* entries: sum_i f = P_k (N-k) <= P0 N + Pmax */
  cap += (size_t)Pmax;
  uint16_t *F = malloc(cap * 2), *F2 = malloc(cap * 2);
  int8_t *J = malloc(cap), *J2 = malloc(cap);
  long P = P0;
  int *V = malloc(sizeof(int) * (Pmax + P0 + 1));
  for (long i = 0; i < P; i++) for (int m = 0; m < N; m++) { F[i * N + m] = m + 1; J[i * N + m] = 0; }
  double logZ = 0;
  for (int k = 0; k < N; k++) {
    int f = N - k;
    double sum = 0;
    for (long i = 0; i < P; i++) {
      const int8_t *j = J + i * f; int v = 0;
      for (int m = 0; m < f; m++) v += (j[m] == 0);
      V[i] = v; sum += v;
    }
    if (sum == 0) { printf("N=%d extinct at k=%d\n", N, k); return 0; }
    logZ += log(sum / P);
    if (sf && k > 0 && (int)((long)k * 64 / N) != (int)((long)(k - 1) * 64 / N)) {
      /* diagnostics: acceptance, sd and mean of J on free panels, max |E|, and the structure
       * function SE(l) = mean_x (E(x+l)-E(x))^2 of the discrepancy E(x) = P(x) - k x/N
       * (cyclic, l = 2^j), all averaged over particles. */
      double fr = 0, sdj = 0, mj = 0, dm = 0, se[24] = {0}; int nl = 0; while ((2 << nl) <= N) nl++;
      double *E = malloc(sizeof(double) * (N + 1));
      long nd = P < 400 ? P : 400;            /* diagnostics on an evenly spaced subsample */
      for (long ii = 0; ii < nd; ii++) {
        long i = ii * P / nd;
        const int8_t *j = J + i * f; const uint16_t *fr_ = F + i * f;
        double s1 = 0, s2 = 0;
        for (int m = 0; m < f; m++) { s1 += j[m]; s2 += (double)j[m] * j[m]; }
        fr += V[i] / (double)f; mj += s1 / f; sdj += sqrt(fmax(0, s2 / f - (s1 / f) * (s1 / f)));
        int q = 0, cnt = 0; double d = 0; E[0] = 0;
        for (int x = 1; x <= N; x++) {
          if (q < f && fr_[q] == x) q++; else cnt++;
          E[x] = cnt - (double)k * x / N; if (fabs(E[x]) > d) d = fabs(E[x]);
        }
        dm += d;
        for (int l = 0; l < nl; l++) {
          int L = 1 << l; double a = 0;
          for (int x = 0; x < N; x++) { int y = x + L; double e2 = y <= N ? E[y] : E[y - N]; a += (e2 - E[x]) * (e2 - E[x]); }
          se[l] += a / N;
        }
      }
      free(E);
      fprintf(sf, "k=%d t=%.4f P=%ld meanV=%.4f logZ=%.4f frac=%.5f sdJ=%.4f meanJ=%.4f Dmax=%.4f SE=", k,
              (double)k / N, P, sum / P, logZ, fr / nd, sdj / nd, mj / nd, dm / nd);
      for (int l = 0; l < nl; l++) fprintf(sf, "%s%.4f", l ? "," : "", se[l] / nd);
      fprintf(sf, "\n"); fflush(sf);
    }
    if (f == 1) break;
    long Pn = (long)((double)P0 * N / (f - 1)); if (Pn > Pmax) Pn = Pmax; if (Pn < P0) Pn = P0;
    int g = f - 1;
    double step = sum / Pn, u = urand() * step, acc = 0; long jx = 0;
    for (long i = 0; i < Pn; i++) {
      double target = u + i * step;
      while (acc + V[jx] <= target) { acc += V[jx]; jx++; }
      const uint16_t *sF = F + jx * f; const int8_t *sJ = J + jx * f;
      uint16_t *dF = F2 + i * g; int8_t *dJ = J2 + i * g;
      int r = rnd() % V[jx], xi = 0;
      for (int m = 0; m < f; m++) if (sJ[m] == 0) { if (r-- == 0) { xi = m; break; } }
      int x = sF[xi], a = (x + 2) / 2, b = (N + x) / 2;
      for (int m = 0; m < xi; m++) { dF[m] = sF[m]; dJ[m] = sJ[m] + (sF[m] >= a); }
      for (int m = xi + 1; m < f; m++) { dF[m - 1] = sF[m]; dJ[m - 1] = sJ[m] - (sF[m] <= b); }
    }
    uint16_t *t = F; F = F2; F2 = t; int8_t *t2 = J; J = J2; J2 = t2;
    P = Pn;
  }
  double lf = lgamma(N + 1.0);
  printf("N=%d P=%ld Pmax=%ld loga_est=%.4f logN!=%.4f ratio=%.5f deficit=%.5f\n", N, P0, Pmax, logZ, lf,
         logZ / lf, (lf - logZ) / N);
  return 0;
}

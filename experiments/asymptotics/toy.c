/* toy.c -- the "soft" Feynman-Kac model behind section 2 of NOTES.txt.
 *
 *   usage: ./toy N P seed
 *
 * Random permutations (each step: a uniformly random FREE panel, valid or not) weighted by
 *   prod_k  f_k / (sqrt(2 pi) sigma_J(S_k))          (f_k = N - k free panels),
 * i.e. the true constraint 1[J(x_k) = 0] is replaced by its local-CLT average.  If the
 * mechanism of section 2 is complete, sigma_J along this model grows like the true one.
 * The J field is updated by the same dipole rule.  Population SMC as in smc3.c (fixed P).
 * Prints sigma_J at t = 1/4, 1/2, 3/4, sigma_bar = exp(mean_t ln sigma_J) and the log weight.
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
  if (argc < 3) { fprintf(stderr, "usage: toy N P seed\n"); return 1; }
  int N = atoi(argv[1]); long P = atol(argv[2]);
  rs = (argc > 3 ? strtoull(argv[3], 0, 10) : 1) * 2654435761ULL + 88172645463325252ULL;
  for (int i = 0; i < 10; i++) rnd();
  uint16_t *F = malloc(2 * P * N), *F2 = malloc(2 * P * N);
  int16_t *J = malloc(2 * P * N), *J2 = malloc(2 * P * N);
  double *W = malloc(sizeof(double) * P), *SG = malloc(sizeof(double) * P);
  for (long i = 0; i < P; i++) for (int m = 0; m < N; m++) { F[i * N + m] = m + 1; J[i * N + m] = 0; }
  double logZ = 0, lsum = 0; int nl = 0; double s14 = 0, s12 = 0, s34 = 0;
  for (int k = 0; k < N - 1; k++) {
    int f = N - k; double sum = 0, ssum = 0;
    for (long i = 0; i < P; i++) {
      const int16_t *j = J + i * f; double s1 = 0, s2 = 0;
      for (int m = 0; m < f; m++) { s1 += j[m]; s2 += (double)j[m] * j[m]; }
      double sg = sqrt(fmax(0, s2 / f - (s1 / f) * (s1 / f)));
      double p = 1.0 / (sqrt(2 * M_PI) * fmax(sg, 0.4)); if (p > 1) p = 1;
      SG[i] = sg; W[i] = f * p; sum += W[i]; ssum += sg;
    }
    logZ += log(sum / P);
    if (k > 0 && k < N - 1 && k % (N / 64 ? N / 64 : 1) == 0) { lsum += log(ssum / P); nl++; }
    if (4 * k == N) s14 = ssum / P;
    if (2 * k == N) s12 = ssum / P;
    if (4 * k == 3 * N) s34 = ssum / P;
    int g = f - 1;
    double step = sum / P, u = urand() * step, acc = 0; long jx = 0;
    for (long i = 0; i < P; i++) {
      double target = u + i * step;
      while (jx < P - 1 && acc + W[jx] <= target) { acc += W[jx]; jx++; }
      const uint16_t *sF = F + jx * f; const int16_t *sJ = J + jx * f;
      uint16_t *dF = F2 + i * g; int16_t *dJ = J2 + i * g;
      int xi = rnd() % f;
      int x = sF[xi], a = (x + 2) / 2, b = (N + x) / 2;
      for (int m = 0; m < xi; m++) { dF[m] = sF[m]; dJ[m] = sJ[m] + (sF[m] >= a); }
      for (int m = xi + 1; m < f; m++) { dF[m - 1] = sF[m]; dJ[m - 1] = sJ[m] - (sF[m] <= b); }
    }
    uint16_t *t = F; F = F2; F2 = t; int16_t *t2 = J; J = J2; J2 = t2;
  }
  printf("N=%d P=%ld toy_logw=%.3f deficit=%.4f sigma(1/4)=%.3f sigma(1/2)=%.3f sigma(3/4)=%.3f sigma_bar=%.3f\n",
         N, P, logZ, (lgamma(N + 1.0) - logZ) / N, s14, s12, s34, exp(lsum / nl));
  return 0;
}

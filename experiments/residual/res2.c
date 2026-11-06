/* res2.c N1 N2 STEP FAMS [verbose]: residual after the old regions and the PF cells
   (orientation (u', u), direction (p, 1), p = 1, 2) for the families in FAMS (bitmask: 1 = Z, 2 = X0, 4 = X1).
   verbose 1: print leftover pairs; 2: also a map. */
#include "pfcore.h"
static int FAMS;
static int cell(ll N, ll u, ll up) {
  for (int f = 0; f < 3; f++) {
    if (!(FAMS >> f & 1)) continue;
    ll K, R, al, be, smax, amin;
    comboParams(N, u, f, &K, &R, &al, &be, &smax, &amin);
    buildPi(K, up, R, al, be, smax, amin);
    if (testDir(1, 1) == 2 || testDir(2, 1) == 2) return 1;
  }
  return 0;
}
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]), STEP = atoll(argv[3]);
  FAMS = atoi(argv[4]);
  int verbose = argc > 5 ? atoi(argv[5]) : 0;
  ll GT = 0, GR = 0, GL = 0;
  for (ll N = N1; N <= N2; N += STEP) {
    ll tot = 0, res = 0, left = 0;
    for (ll u = 2; 3 * u + 1 <= N; u++)
      for (ll up = u; u + 2 * up <= N - 1; up++) {
        if (!isPair(N, u, up)) continue;
        tot++;
        if (provenOld(N, u, up)) continue;
        res++;
        if (cell(N, u, up)) continue;
        left++;
        if (verbose) printf("L N=%lld u=%lld u'=%lld d=%lld delta=%lld r=%.3f\n", N, u, up, up - u, N - 1 - u - 2 * up, (double)up / u);
      }
    GT += tot; GR += res; GL += left;
    printf("N=%lld tot %lld oldres %lld left %lld\n", N, tot, res, left);
  }
  printf("all: tot %lld oldres %lld left %lld\n", GT, GR, GL);
  return 0;
}

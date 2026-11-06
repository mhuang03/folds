/* res3.c N1 N2 STEP QMAX [verbose]: the Lean residual `Residual2` (pairs outside Proven2 =
   old regions + RegionPF; RegionPF tested with directions q <= QMAX, so this is an upper bound),
   exact (parok.h).  Sanity: every RegionPF pair passes dirAny in some orientation.
   verbose 1: print the remaining pairs. */
#include "parok.h"
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]), STEP = atoll(argv[3]);
  QMAXP = atoi(argv[4]);
  int verbose = argc > 5 ? atoi(argv[5]) : 0;
  ll GT = 0, GO = 0, GL = 0, bad = 0;
  for (ll N = N1; N <= N2; N += STEP) {
    ll tot = 0, old = 0, left = 0;
    for (ll u = 2; 3 * u + 1 <= N; u++)
      for (ll up = u; u + 2 * up <= N - 1; up++) {
        if (!isPair(N, u, up)) continue;
        tot++;
        if (provenOld(N, u, up)) continue;
        old++;
        if (regionPF(N, u, up)) {
          if (!dirAny(N, u, up) && !dirAny(N, up, u)) { bad++; printf("BAD N=%lld u=%lld u'=%lld\n", N, u, up); }
          continue;
        }
        left++;
        if (verbose) printf("L N=%lld u=%lld u'=%lld d=%lld delta=%lld\n", N, u, up, up - u, N - 1 - u - 2 * up);
      }
    GT += tot; GO += old; GL += left;
    if (verbose || N % 100 == 0 || N == N2 || STEP > 1) printf("N=%lld tot %lld oldres %lld left %lld\n", N, tot, old, left);
  }
  printf("all: tot %lld oldres %lld left %lld bad %lld\n", GT, GO, GL, bad);
  return 0;
}

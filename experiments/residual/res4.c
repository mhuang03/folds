/* res4.c N1 N2 STEP [verbose]: residual after old regions, RegionPF (q <= 3) and RegionSL
   (slices a = p c + j, p <= 3, directions in (s, c) with c-step <= 4, s-step <= 16).
   Sanity: every newly covered pair passes dirAny. */
#include "slice.h"
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]), STEP = atoll(argv[3]);
  int verbose = argc > 4 ? atoi(argv[4]) : 0;
  QMAXP = 3;
  ll GT = 0, GO = 0, GP = 0, GL = 0, bad = 0;
  for (ll N = N1; N <= N2; N += STEP) {
    ll tot = 0, old = 0, pf = 0, left = 0;
    for (ll u = 2; 3 * u + 1 <= N; u++)
      for (ll up = u; u + 2 * up <= N - 1; up++) {
        if (!isPair(N, u, up)) continue;
        tot++;
        if (provenOld(N, u, up)) continue;
        old++;
        if (regionPF(N, u, up)) continue;
        pf++;
        if (regionSL(N, u, up)) {
          if (!dirAny(N, u, up) && !dirAny(N, up, u)) { bad++; printf("BAD N=%lld u=%lld u'=%lld\n", N, u, up); }
          continue;
        }
        left++;
        if (verbose) printf("L N=%lld u=%lld u'=%lld d=%lld delta=%lld\n", N, u, up, up - u, N - 1 - u - 2 * up);
      }
    GT += tot; GO += old; GP += pf; GL += left;
    if (verbose || N == N2 || STEP > 1 || N % 100 == 0) printf("N=%lld tot %lld oldres %lld afterPF %lld left %lld\n", N, tot, old, pf, left);
  }
  printf("all: tot %lld oldres %lld afterPF %lld left %lld bad %lld\n", GT, GO, GP, GL, bad);
  return 0;
}

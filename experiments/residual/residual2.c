/* residual2.c N1 N2 STEP [verbose]: Lean's Residual2 (the pairs outside Proven2 = old regions
   + RegionPF + RegionSL + RegionS), with RegionPF / RegionSL tested on the directions of
   parok.h / slice.h (so the count is an upper bound for the pairs outside Proven2).
   Sanity: every pair covered by PF / SL passes dirAny. */
#include "slice.h"
static int regionS(ll N, ll u, ll up) {
  if (N < 301) return 0;
  if (u == 2 && (up == 4 || up == 5)) return 1;
  if (u == 3 && up >= 5 && up <= 8) return 1;
  if (u == 5 && up == 5) return 1;
  if (u == 3 && (N + 1 == 3 * up || N + 3 == 3 * up || N + 5 == 3 * up || N == 3 * up + 1 ||
                 N == 3 * up + 3 || N == 3 * up + 5)) return 1;
  if (N == 3 * up && u + 1 == up) return 1;
  return 0;
}
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]), STEP = atoll(argv[3]);
  int verbose = argc > 4 ? atoi(argv[4]) : 0;
  QMAXP = 3;
  ll GT = 0, GO = 0, GPF = 0, GSL = 0, GS = 0, GL = 0, bad = 0;
  for (ll N = N1; N <= N2; N += STEP) {
    ll tot = 0, old = 0, pf = 0, sl = 0, sh = 0, left = 0;
    for (ll u = 2; 3 * u + 1 <= N; u++)
      for (ll up = u; u + 2 * up <= N - 1; up++) {
        if (!isPair(N, u, up)) continue;
        tot++;
        if (provenOld(N, u, up)) { old++; continue; }
        if (regionPF(N, u, up)) { pf++; if (verbose > 1 && !dirAny(N, u, up) && !dirAny(N, up, u)) bad++; continue; }
        if (regionS(N, u, up)) { sh++; continue; }
        if (regionSL(N, u, up)) {
          sl++;
          if (!dirAny(N, u, up) && !dirAny(N, up, u)) { bad++; printf("BAD N=%lld u=%lld u'=%lld\n", N, u, up); }
          continue;
        }
        left++;
        printf("LEFT N=%lld u=%lld u'=%lld d=%lld delta=%lld\n", N, u, up, up - u, N - 1 - u - 2 * up);
      }
    GT += tot; GO += old; GPF += pf; GSL += sl; GS += sh; GL += left;
    if (verbose || STEP > 1 || N == N2 || N % 100 == 0)
      printf("N=%lld tot %lld old %lld PF %lld S %lld SL %lld left %lld\n", N, tot, old, pf, sh, sl, left);
    fflush(stdout);
  }
  printf("all: tot %lld old %lld PF %lld S %lld SL %lld left %lld bad %lld\n", GT, GO, GPF, GS, GSL, GL, bad);
  return 0;
}

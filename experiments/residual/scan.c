/* scan.c N1 N2 [verbose]: on the residual of the old regions, compare
   E: some (a, c) exact (= dirAny), P: some (a, c) with piOK, J: piOK with |a - c| <= JMAX. */
#include "pi.h"
static int anyPair(ll N, ll u, ll up, int mode, ll jmax) {
  for (int o = 0; o < 2; o++) {
    ll x = o ? up : u, y = o ? u : up;
    for (int f = 0; f < 3; f++) {
      ll K, R, al, be, smax, amin;
      if (f > 0 && y < 2) continue;
      comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
      for (ll c = 1; c * K <= (smax + 1) * (R + 1) + K; c++) {
        /* a near c * x / (R + 1) */
        ll a0 = c * x / (R + 1);
        for (ll a = a0 - 2; a <= a0 + 3; a++) {
          if (mode == 2 && (a - c > jmax || c - a > jmax)) continue;
          if (mode == 0 ? exactOK(K, x, R, al, be, smax, amin, a, c) : piOK(K, x, R, al, be, smax, amin, a, c)) return 1;
        }
      }
    }
  }
  return 0;
}
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  int verbose = argc > 3 ? atoi(argv[3]) : 0;
  ll jmax = argc > 4 ? atoll(argv[4]) : 3;
  for (ll N = N1; N <= N2; N++) {
    ll tot = 0, res = 0, nE = 0, nP = 0, nJ = 0;
    for (ll u = 2; 3 * u + 1 <= N; u++)
      for (ll up = u; u + 2 * up <= N - 1; up++) {
        if (!isPair(N, u, up)) continue;
        tot++;
        if (provenOld(N, u, up)) continue;
        res++;
        int e = anyPair(N, u, up, 0, 0), p = anyPair(N, u, up, 1, 0), j = anyPair(N, u, up, 2, jmax);
        nE += e; nP += p; nJ += j;
        if (verbose && !p) printf("noP N=%lld u=%lld u'=%lld d=%lld delta=%lld\n", N, u, up, up - u, N - 1 - u - 2 * up);
      }
    printf("N=%lld tot %lld res %lld exact %lld pi %lld diag %lld\n", N, tot, res, nE, nP, nJ);
  }
  return 0;
}

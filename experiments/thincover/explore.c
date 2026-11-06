/* explore.c N1 N2 STEP [sk sq] : for each thin point (Lean ThinRest, mixed-parity non-special pair),
   print "N u v cls off old | slice options with ParOK in direction (sk, sq)" where an option is
   o f t p:j (orientation o: 1 = (u', u); family f; t = 0: a = p c + j, t = 1: c = p a + j). */
#include "../residual/slice.h"
static int thinClass(ll N, ll u, ll v, ll *off) {
  if (u <= 3) { *off = u; return 0; }
  if (v <= u + 9) { *off = v - u; return 1; }
  if (2 * u <= v + 12 && v <= 2 * u + 15 && N <= 8 * u + 320) { *off = v - 2 * u; return 2; }
  if (N <= 4 * u + 80 && 4 * u <= N + 40 && N <= u + 2 * v + 81) { *off = 0; return 3; }
  return -1;
}
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]), STEP = atoll(argv[3]);
  ll sk = argc > 4 ? atoll(argv[4]) : 1, sq = argc > 5 ? atoll(argv[5]) : 0;
  for (ll N = N1; N <= N2; N += STEP)
    for (ll u = 2; 3 * u + 1 <= N; u++)
      for (ll v = u; u + 2 * v <= N - 1; v++) {
        if (!isPair(N, u, v)) continue;
        ll off; int c = thinClass(N, u, v, &off);
        if (c < 0) continue;
        if (c == 1 && v == u + 1 && u >= 5 && 3 * u + 21 <= N) continue;
        printf("%lld %lld %lld %d %lld %d |", N, u, v, c, off, provenOld(N, u, v));
        for (int o = 0; o < 2; o++) {
          ll x = o ? v : u, y = o ? u : v;
          for (int f = 0; f < 3; f++) {
            if (f > 0 && y < 3) continue;
            ll K, R, al, be, smax, amin;
            comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
            for (ll p = 0; p <= 3; p++)
              for (int t = 0; t < 2; t++)
                for (ll j = -8; j <= 8; j++) {
                  if (t == 0) buildSlice(K, x, R, al, be, smax, amin, p, j);
                  else buildSliceB(K, x, R, al, be, smax, amin, p, j);
                  if (parOKdir(sk, sq)) printf(" %d%d%d%lld:%lld", o, f, t, p, j);
                }
          }
        }
        printf("\n");
      }
  return 0;
}

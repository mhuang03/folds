/* strip.c N o f p q mode e1 e2 : along strips, min nu-interval length over u.
   mode 0: u' = u + e (diagonal strips), e = e1..e2;  mode 1: u' = 2u + e. */
#include "nuint.h"
static void setup(ll N, ll u, ll up, int o, int f) {
  ll x = o ? up : u, y = o ? u : up;
  ll K, R, al, be, smax, amin;
  comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
  buildCons(K, x, R, al, be, smax, amin);
}
int main(int argc, char **argv) {
  ll N = atoll(argv[1]); int o = atoi(argv[2]), f = atoi(argv[3]); ll p = atoll(argv[4]), q = atoll(argv[5]);
  int mode = atoi(argv[6]); ll e1 = atoll(argv[7]), e2 = atoll(argv[8]);
  for (ll e = e1; e <= e2; e++) {
    printf("e=%3lld:", e);
    /* buckets of u/N in steps of 1/60 */
    for (int b = 0; b < 20; b++) {
      double mnl = 1e18; int any = 0;
      for (ll u = b * N / 60; u < (b + 1) * N / 60; u++) {
        ll up = mode == 0 ? u + e : 2 * u + e;
        if (u < 2 || up < u || u + 2 * up > N - 1) continue;
        if (f > 0 && (o ? u : up) < 3) continue;
        setup(N, u, up, o, f);
        double l = nuLen(nuInterval(p, q));
        if (l < mnl) mnl = l; any = 1;
      }
      if (!any) printf("    ."); else printf(" %4.1f", mnl < -9 ? -9.9 : mnl > 99 ? 99 : mnl);
    }
    printf("\n");
  }
  return 0;
}

/* fam.c N u u' : all witnesses of one pair, compactly: o f a-c (s - u) (s - u') a c s */
#include "common.h"
int main(int argc, char **argv) {
  ll N = atoll(argv[1]), u = atoll(argv[2]), up = atoll(argv[3]);
  printf("N=%lld u=%lld u'=%lld d=%lld delta=%lld N mod 6 = %lld\n", N, u, up, up - u, N - 1 - u - 2 * up, N % 6);
  for (int o = 0; o < 2; o++) {
    ll x = o ? up : u, y = o ? u : up;
    for (int f = 0; f < 3; f++) {
      ll K, R, al, be, smax, amin;
      if (f > 0 && y < 2) continue;
      comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
      for (ll s = (R > 2 ? R : 2); s <= smax; s++) {
        ll a = cdiv(s * x + al, K);
        if (a * K > s * x + al + s - 1 || a < amin) continue;
        ll c = cdiv(s * R + be, K);
        if (c * K > s * R + be + s - 1) continue;
        printf("o=%d f=%d a-c=%lld s-u=%lld s-u'=%lld a=%lld c=%lld s=%lld X=%lld Y=%lld\n", o, f, a - c, s - u, s - up, a, c, s,
               a * K - s * x - al, c * K - s * R - be);
      }
    }
  }
  return 0;
}

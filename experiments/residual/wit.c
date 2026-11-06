/* wit.c N u u' : all witnesses (orientation o (0: (u,u'), 1: (u',u)), family f, a, c, s) */
#include "common.h"
int main(int argc, char **argv) {
  ll N = atoll(argv[1]), u = atoll(argv[2]), up = atoll(argv[3]);
  for (int o = 0; o < 2; o++) {
    ll x = o ? up : u, y = o ? u : up;
    for (int f = 0; f < 3; f++) {
      ll K, R, al, be, smax, amin;
      if (f > 0 && y < 2) continue;
      comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
      for (ll s = (R > 2 ? R : 2); s <= smax; s++) {
        /* a: aK in [s x + al, s x + al + s - 1] */
        ll a = cdiv(s * x + al, K);
        if (a * K > s * x + al + s - 1 || a < amin) continue;
        ll c = cdiv(s * R + be, K);
        if (c * K > s * R + be + s - 1) continue;
        printf("o=%d f=%d a=%lld c=%lld s=%lld  (s/K=%.4f)\n", o, f, a, c, s, (double)s / K);
      }
    }
  }
  return 0;
}

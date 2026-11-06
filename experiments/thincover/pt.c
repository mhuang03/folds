/* pt.c N u v : all ParOK options for one pair: famCons (o, f, dir) and slices (o, f, t, p, j, dir). */
#include "../residual/slice.h"
int main(int argc, char **argv) {
  ll N = atoll(argv[1]), u = atoll(argv[2]), v = atoll(argv[3]);
  printf("pair %d old %d\n", isPair(N, u, v), provenOld(N, u, v));
  for (int o = 0; o < 2; o++) {
    ll x = o ? v : u, y = o ? u : v;
    for (int f = 0; f < 3; f++) {
      if (f > 0 && y < 3) continue;
      ll K, R, al, be, smax, amin;
      comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
      buildCons(K, x, R, al, be, smax, amin);
      for (ll q = 0; q <= 8; q++)
        for (ll p = (q == 0 ? 1 : -3 * q); p <= (q == 0 ? 1 : 3 * q + 3); p++)
          if (parOKdir(p, q)) printf("PF o%d f%d dir(%lld,%lld)\n", o, f, p, q);
      for (ll p = 0; p <= 3; p++)
        for (int t = 0; t < 2; t++)
          for (ll j = -12; j <= 12; j++) {
            for (ll k = 0; k <= 4; k++)
              for (ll sg = (k == 0 ? 1 : -40); sg <= (k == 0 ? 1 : 40); sg++) {
                if (t == 0) buildSlice(K, x, R, al, be, smax, amin, p, j);
                else buildSliceB(K, x, R, al, be, smax, amin, p, j);
                if (parOKdir(sg, k)) printf("SL o%d f%d t%d p%lld j%lld dir(%lld,%lld)\n", o, f, t, p, j, sg, k);
              }
          }
    }
  }
  return 0;
}

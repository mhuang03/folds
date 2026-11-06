/* cluster2.c N1 N2 STEP : the cluster box, per point "N u v r delta bits" where bits is a 0/1
   string over (o, f, dir) for o in {0,1}, f in {0,1,2}, dir in DIRS: ParOK of famCons with side dir. */
#include "../residual/parok.h"
static ll DIRS[][2] = {{1,1},{2,1},{3,2},{3,1},{4,3},{5,3},{1,2},{2,3},{3,4},{5,7},{1,0},{0,1},{4,1},{5,2},{5,4},{7,4}};
#define ND ((int)(sizeof DIRS / sizeof DIRS[0]))
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]), STEP = atoll(argv[3]);
  for (ll N = N1; N <= N2; N += STEP)
    for (ll u = 4; 3 * u + 1 <= N; u++)
      for (ll v = u + 10; u + 2 * v <= N - 1; v++) {
        if (!isPair(N, u, v)) continue;
        if (2 * u <= v + 12 && v <= 2 * u + 15 && N <= 8 * u + 320) continue;
        if (!(N <= 4 * u + 80 && 4 * u <= N + 40 && N <= u + 2 * v + 81)) continue;
        char bits[6 * ND + 1];
        int b = 0;
        for (int o = 0; o < 2; o++)
          for (int f = 0; f < 3; f++) {
            ll x = o ? v : u, y = o ? u : v;
            ll K, R, al, be, smax, amin;
            comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
            buildCons(K, x, R, al, be, smax, amin);
            for (int d = 0; d < ND; d++) bits[b++] = parOKdir(DIRS[d][0], DIRS[d][1]) ? '1' : '0';
          }
        bits[b] = 0;
        printf("%lld %lld %lld %lld %lld %s\n", N, u, v, 4 * u - N, N - 1 - u - 2 * v, bits);
      }
  return 0;
}

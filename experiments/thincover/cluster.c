/* cluster.c N1 N2 STEP : the cluster box (Lean `Thin`, 4th clause, outside the diagonal / strip
   clauses), per point: N r = 4u - N, delta = N - 1 - u - 2v, and flags
   old regions (B B2 W D D0), keys A B4 B1 (Z o1), the edge library index (first that works, or -1),
   ParOK of famCons (Z/X0/X1, both orientations) with side (3,2) resp. (2,3). */
#include "../coverall/keys.h"
typedef struct { int f, o; ll p, q; int e; } KC;
static KC kc[] = {
  {0,1,1,1,4},{0,1,2,1,4},{0,1,2,1,1},{1,1,1,1,4},{1,1,2,1,4},{1,1,2,1,1},{2,1,1,1,4},{2,1,2,1,4},{2,1,2,1,1},
  {0,1,3,2,4},{0,1,3,2,1},{1,1,3,2,4},{1,1,3,2,1},{0,1,1,1,1},{1,1,1,1,1},
  {0,0,1,1,4},{0,0,1,1,1},{1,0,1,1,4},{1,0,1,1,1},{0,1,3,1,4},{0,1,3,1,1},{1,1,3,1,1},{1,1,3,1,4},
  {0,1,4,3,4},{0,1,4,3,1},{1,1,4,3,4},{1,1,4,3,1},{0,1,5,3,1},{0,1,5,3,4},{1,1,5,3,1},{1,1,5,3,4}};
#define NK ((int)(sizeof kc / sizeof kc[0]))
static int testK(ll N, ll u, ll up, KC k) {
  ll x = k.o ? up : u, y = k.o ? u : up;
  if (k.f > 0 && y < 3) return 0;
  Fam f = k.f == 0 ? famZo(N, x, y) : k.f == 1 ? famX0o(N, x, y) : famX1o(N, x, y);
  return k.e == 4 ? edge4Keys(f, k.p, k.q) : edge1Keys(f, k.p, k.q);
}
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]), STEP = atoll(argv[3]);
  for (ll N = N1; N <= N2; N += STEP)
    for (ll u = 4; 3 * u + 1 <= N; u++)
      for (ll v = u + 10; u + 2 * v <= N - 1; v++) {
        if (!isPair(N, u, v)) continue;
        if (2 * u <= v + 12 && v <= 2 * u + 15 && N <= 8 * u + 320) continue;
        if (!(N <= 4 * u + 80 && 4 * u <= N + 40 && N <= u + 2 * v + 81)) continue;
        int ob = regB(N, u, v) | regB2(N, u, v) << 1 | regW(N, u, v) << 2 | regD(N, u, v) << 3 | regD0(N, u, v) << 4;
        long k = 0;
        for (int i = 0; i < NK; i++) if (testK(N, u, v, kc[i])) k |= 1L << i;
        int pf = 0, bit = 1;
        for (int o = 0; o < 2; o++)
          for (int f = 0; f < 3; f++, bit <<= 1) {
            ll x = o ? v : u, y = o ? u : v;
            ll K, R, al, be, smax, amin;
            comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
            buildCons(K, x, R, al, be, smax, amin);
            if (o ? parOKdir(3, 2) : parOKdir(2, 3)) pf |= bit;
          }
        printf("%lld %lld %lld %lld %lld %d %d %d %d %ld %d\n", N, u, v, 4 * u - N, N - 1 - u - 2 * v, ob,
               keyA(N, u, v), keyB4(N, u, v), keyB1(N, u, v), k, pf);
      }
  return 0;
}

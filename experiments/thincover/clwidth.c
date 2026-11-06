/* clwidth.c N1 N2 STEP o f p q [o f p q ...] : the cluster box; per point "N r delta w1 w2 ..."
   with w = (nu-window length) - 1 of ParOK(famCons) with side (p, q) (negative: no ParOK). */
#include "../residual/parok.h"
static double nuwidth(ll p1, ll q1) {
  ll x, y;
  if (egcd2(p1, q1, &x, &y) != 1) return -99;
  ll p2 = -y, q2 = x;
  LL g1[16], g2[16];
  for (int i = 0; i < ng; i++) { g1[i] = gs[i].A * p1 + gs[i].C * q1; g2[i] = gs[i].A * p2 + gs[i].C * q2; }
  int haveLo = 0, haveHi = 0;
  LL loN = 0, loD = 1, hiN = 0, hiD = 1;
#define ADDC2(E, F) do { LL e_ = (E), f_ = (F); \
    if (e_ == 0) { if (f_ > 0) return -99; } \
    else if (e_ > 0) { if (!haveLo || fcmp(f_, e_, loN, loD) > 0) { loN = f_; loD = e_; haveLo = 1; } } \
    else { if (!haveHi || fcmp(-f_, -e_, hiN, hiD) < 0) { hiN = -f_; hiD = -e_; haveHi = 1; } } } while (0)
  for (int i = 0; i < ng; i++) if (g1[i] == 0) ADDC2(g2[i], -gs[i].D);
  for (int i = 0; i < ng; i++) {
    if (g1[i] <= 0) continue;
    for (int k = 0; k < ng; k++) {
      if (g1[k] >= 0) continue;
      LL a1 = g1[i], b1 = -g1[k];
      ADDC2(a1 * g2[k] + b1 * g2[i], a1 * b1 - a1 * gs[k].D - b1 * gs[i].D);
    }
  }
  if (!haveLo || !haveHi) return -99;
  return (double)hiN / (double)hiD - (double)loN / (double)loD - 1.0;
}
static ll ALLD[][2] = {{1,1},{2,1},{3,2},{1,2},{2,3},{3,1},{4,3},{5,3},{3,4},{5,4},{1,0},{0,1}};
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]), STEP = atoll(argv[3]);
  int nc = (argc - 4) / 4;
  static char *av[1000];
  static char buf[1000][8];
  if (argc > 4 && argv[4][0] == 'a') {
    int k = 0;
    for (int o = 0; o < 2; o++) for (int f = 0; f < 3; f++) for (int d = 0; d < 12; d++) {
      sprintf(buf[k], "%d", o); av[4 + k] = buf[k]; k++;
      sprintf(buf[k], "%d", f); av[4 + k] = buf[k]; k++;
      sprintf(buf[k], "%lld", ALLD[d][0]); av[4 + k] = buf[k]; k++;
      sprintf(buf[k], "%lld", ALLD[d][1]); av[4 + k] = buf[k]; k++;
    }
    nc = k / 4;
    argv = av;
  }
  for (ll N = N1; N <= N2; N += STEP)
    for (ll u = (N - 80) / 4; 4 * u <= N + 40; u++)
      for (ll v = u + 10; u + 2 * v <= N - 1; v++) {
        if (N - 1 - u - 2 * v > 80) continue;
        if (!(N <= 4 * u + 80) || v + 13 > 2 * u) continue;
        printf("%lld %lld %lld %d", N, 4 * u - N, N - 1 - u - 2 * v, isPair(N, u, v));
        for (int c = 0; c < nc; c++) {
          int o = atoi(argv[4 + 4 * c]), f = atoi(argv[5 + 4 * c]);
          ll p = atoll(argv[6 + 4 * c]), q = atoll(argv[7 + 4 * c]);
          ll x = o ? v : u, y = o ? u : v;
          ll K, R, al, be, smax, amin;
          comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
          /* Lean lower bound of smax: Z (N+1)/2, X0 N/2, X1 (N-1)/2 -> use floor-free halves: scale */
          buildCons(K, x, R, al, be, smax, amin);
          printf(" %.4f", nuwidth(p, q));
        }
        printf("\n");
      }
  return 0;
}

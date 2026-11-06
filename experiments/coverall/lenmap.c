/* lenmap.c N o f p q G : for the candidate (orientation o, family f, w1 = (p, q)), grid map over
   (u/N, u'/N) of the minimum nu-interval length (digit = floor(len), '+' >= 10, '-' < 0 or none),
   then a list of the defining pairs for a few sample points. */
#include "nuint.h"
static void setup(ll N, ll u, ll up, int o, int f) {
  ll x = o ? up : u, y = o ? u : up;
  ll K, R, al, be, smax, amin;
  comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
  buildCons(K, x, R, al, be, smax, amin);
}
int main(int argc, char **argv) {
  ll N = atoll(argv[1]); int o = atoi(argv[2]), f = atoi(argv[3]); ll p = atoll(argv[4]), q = atoll(argv[5]);
  int G = argc > 6 ? atoi(argv[6]) : 60;
  static double mn[300][300]; static int seen[300][300];
  for (ll u = 2; 3 * u + 1 <= N; u++)
    for (ll up = u; u + 2 * up <= N - 1; up++) {
      if (f > 0 && (o ? u : up) < 3) continue;
      setup(N, u, up, o, f);
      NuI r = nuInterval(p, q);
      double l = nuLen(r);
      int i = u * G / N, j = up * G / N;
      if (!seen[i][j] || l < mn[i][j]) mn[i][j] = l;
      seen[i][j] = 1;
    }
  for (int j = G / 2; j >= 0; j--) {
    printf("%5.3f ", (double)j / G);
    for (int i = 0; i <= G / 3; i++) {
      char ch = ' ';
      if (seen[i][j]) { double l = mn[i][j]; ch = l < 0 ? '-' : l >= 10 ? '+' : '0' + (int)l; }
      putchar(ch);
    }
    printf("\n");
  }
  return 0;
}

/* cmap.c N o f p q [mode]: map of the residual (of the old regions) in (u/N, u'/N):
   '#' = PF for this candidate, 'e' = EX only, '.' = residual not covered, '_' = not residual.
   mode 1: the candidate (o, f, p, q) is replaced by "any f" (f ignored). */
#include "pfcore.h"
int main(int argc, char **argv) {
  ll N = atoll(argv[1]);
  int o = atoi(argv[2]), f = atoi(argv[3]), p = atoi(argv[4]), q = atoi(argv[5]);
  int mode = argc > 6 ? atoi(argv[6]) : 0;
  int G = 90;
  static int st[200][200]; /* bit0: residual seen, bit1: covered, bit2: uncovered */
  for (ll u = 2; 3 * u + 1 <= N; u++)
    for (ll up = u; u + 2 * up <= N - 1; up++) {
      if (!isPair(N, u, up)) continue;
      int i = u * G / N, j = up * G / N;
      if (provenOld(N, u, up)) { st[i][j] |= 8; continue; }
      int r = 0;
      for (int ff = 0; ff < 3; ff++) {
        if (!mode && ff != f) continue;
        ll x = o ? up : u, y = o ? u : up;
        ll K, R, al, be, smax, amin;
        if (ff > 0 && y < 2) continue;
        comboParams(N, y, ff, &K, &R, &al, &be, &smax, &amin);
        buildPi(K, x, R, al, be, smax, amin);
        int t = testDir(p, q);
        if (t > r) r = t;
      }
      st[i][j] |= (r == 2 ? 2 : 4);
    }
  for (int j = G / 2; j >= 0; j--) {
    printf("%5.3f ", (double)j / G);
    for (int i = 0; i <= G / 3; i++) {
      int s = st[i][j];
      char ch = ' ';
      if (s & 4) ch = (s & 2) ? '+' : '.';
      else if (s & 2) ch = '#';
      else if (s & 8) ch = '_';
      putchar(ch);
    }
    printf("\n");
  }
  return 0;
}

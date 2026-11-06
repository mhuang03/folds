/* clcost2.c N1 N2 : for the cluster pairs, the success set of dirAll in orientation (u, v) and
   (v, u): prints, over all points, min and max of (a1 - N/16) etc., to choose a search start g. */
#include "../residual/common.h"
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  double lo1 = 1e9, hi1 = -1e9;
  long tot = 0, both = 0, onlyB = 0, nonint = 0;
  for (ll N = N1; N <= N2; N++)
    for (ll u = (N - 80) / 4; 4 * u <= N + 40; u++)
      for (ll v = u + 10; u + 2 * v + 1 <= N; v++) {
        if (!(N <= 4 * u + 80 && N <= u + 2 * v + 81 && v + 13 <= 2 * u && (u + (N + 1 - v)) % 2 == 1)) continue;
        tot++;
        ll a1 = -1, a2 = -1, last = -1;
        for (ll a = 1; a <= u + 1; a++) if (dirAll(N, u, v, a)) { if (a1 < 0) a1 = a; if (last >= 0 && a != last + 1) nonint++; last = a; a2 = a; }
        if (a1 < 0) { onlyB++; continue; }
        /* guess g = (u * (N/2 - ...)) : use ratio a1 / u */
        double r1 = (double)a1 * N / ((double)u * N);
        (void)r1;
        double g = (double)u * atof(argv[3]);
        double d = a1 - g;
        if (d < lo1) lo1 = d;
        if (a1 - g > hi1) hi1 = a1 - g;
        (void)both;
      }
  printf("tot %ld onlyB %ld nonint %ld  a1 - 0.3u in [%.1f, ..], a2 - 0.3u max %.1f\n", tot, onlyB, nonint, lo1, hi1);
  return 0;
}

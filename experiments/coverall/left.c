/* left.c N1 N2 STEP [all] : pairs (u <= u', u + 2u' <= N - 1, u >= 2; parity ignored unless
   `all` = 0 -> only mixed-parity non-special) outside the old regions and not covered by the bulk
   key conditions A, B4, B1.  Prints a summary by class: diagonal d <= 12, e-strip |u' - 2u| <= 20,
   other (listed with offsets from N/4, 3N/8 and N/8, N/4). */
#include "keys.h"
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]), STEP = atoll(argv[3]);
  int par = argc > 4 ? atoi(argv[4]) : 1;
  for (ll N = N1; N <= N2; N += STEP) {
    ll dg[13] = {0}, es[41] = {0}, oth = 0, tot = 0;
    ll emin = 1 << 30;
    for (ll u = 2; 3 * u + 1 <= N; u++)
      for (ll up = u; u + 2 * up <= N - 1; up++) {
        if (par && !isPair(N, u, up)) continue;
        if (!par && special(N, u, up)) continue;
        if (provenOld(N, u, up)) continue;
        if (keyA(N, u, up) || keyB4(N, u, up) || keyB1(N, u, up)) continue;
        tot++;
        ll d = up - u, e = up - 2 * u;
        if (d <= 12) { dg[d]++; continue; }
        if (e >= -20 && e <= 20) { es[e + 20]++; if (u < emin) emin = u; continue; }
        oth++;
        if (oth <= 40) printf("  other u=%lld u'=%lld  u-N/4=%lld u'-3N/8=%lld delta=%lld  u-N/8=%lld e=%lld\n",
                              u, up, u - N / 4, up - 3 * N / 8, N - 1 - u - 2 * up, u - N / 8, e);
      }
    printf("N=%lld left %lld  diag:", N, tot);
    for (int d = 0; d <= 12; d++) if (dg[d]) printf(" d%d:%lld", d, dg[d]);
    printf("  e:");
    for (int e = 0; e <= 40; e++) if (es[e]) printf(" %d:%lld", e - 20, es[e]);
    printf("  (e-strip min u = %lld, N/8 = %lld)  other %lld\n", emin, N / 8, oth);
    fflush(stdout);
  }
  return 0;
}

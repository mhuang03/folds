/* bulk.c N1 N2 STEP : the bulk claim.  For every (u, u'), 4 <= u <= u', u + 2u' <= N - 1 (any
   parity, non-special), outside the thin sets THIN(N, u, u'), one of: old region, keyA, keyB4,
   keyB1.  Prints failures. */
#include "keys.h"
static int thin(ll N, ll u, ll up) {
  ll d = up - u, e = up - 2 * u, del = N - 1 - u - 2 * up;
  if (u <= 3) return 1;
  if (d <= 9) return 1;                                       /* Diag */
  if (e >= -12 && e <= 15 && 8 * u + 60 >= N) return 1;       /* Estrip */
  if (4 * u + 80 >= N && 4 * u <= N + 40 && del <= 80) return 1; /* Cluster */
  return 0;
}
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]), STEP = atoll(argv[3]);
  ll bad = 0;
  for (ll N = N1; N <= N2; N += STEP) {
    ll nb = 0;
    for (ll u = 2; 3 * u + 1 <= N; u++)
      for (ll up = u; u + 2 * up <= N - 1; up++) {
        if (special(N, u, up) || thin(N, u, up)) continue;
        if (provenOld(N, u, up)) continue;
        if (keyA(N, u, up) || keyB4(N, u, up) || keyB1(N, u, up)) continue;
        nb++;
        if (nb <= 5) printf("FAIL N=%lld u=%lld u'=%lld d=%lld e=%lld del=%lld\n", N, u, up, up - u, up - 2 * u, N - 1 - u - 2 * up);
      }
    bad += nb;
    if (nb || N % 500 < STEP) { printf("N=%lld fails %lld\n", N, nb); fflush(stdout); }
  }
  printf("total fails %lld\n", bad);
  return 0;
}

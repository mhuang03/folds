/* small2.c N1 N2 : check the planned cover of the class u <= 3 (u = 2, 3) by old regions:
   u = 2: u' in {4,5} RegionS, u' >= 6 D0;
   u = 3: u' in [5,8] RegionS, u' in {9,10} shapes, N - 3u' >= 7 D0, |N - 3u'| <= 5 RegionS,
          N - 3u' <= -7: B2 if 8u' <= 3N + 2, else B.  Prints failures. */
#include "../residual/common.h"
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  long fails = 0, tot = 0;
  for (ll N = N1; N <= N2; N++)
    for (ll u = 2; u <= 3; u++)
      for (ll v = u; u + 2 * v <= N - 1; v++) {
        if (!isPair(N, u, v)) continue;
        tot++;
        int ok;
        ll m = N - 3 * v;
        if (u == 2) ok = (v == 4 || v == 5) ? 1 : (v >= 6 && regD0(N, u, v));
        else if (v <= 8) ok = v >= 5;
        else if (v <= 10) ok = 2;
        else if (m >= 7) ok = regD0(N, u, v);
        else if (m >= -5) ok = 1;
        else if (8 * v <= 3 * N + 2) ok = regB2(N, u, v);
        else ok = regB(N, u, v);
        if (!ok) { fails++; if (fails < 20) printf("fail N=%lld u=%lld v=%lld m=%lld\n", N, u, v, m); }
      }
  printf("tot %ld fails %ld\n", tot, fails);
  return 0;
}

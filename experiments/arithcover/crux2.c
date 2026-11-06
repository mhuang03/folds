/* crux2.c N1 N2 [step]: Corollary B': N >= 301, 3 <= u, u^2 <= N, u + 2u' <= N - 1, 8u' >= 3N + 2,
   not (u = 3, 2u' + 4 = N)  ==>  region B.  (Any parity; prints counterexamples.) */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static int regB(ll N, ll u, ll up) {
  ll M = N + 2, n = M - 2 * up, c = u / 2;
  if (u < 3 || n < 3) return 0;
  if ((u + 1) * (n - 1) > c * M) return 0;
  if (u * (u + 1) > c * M) return 0;
  if (c * M * (n + 2 * u) < u * ((2 * u + 1) * n - 2 * u) + u * (u + 1) * (2 * n + M - 1)) return 0;
  if (2 * (u + 1) > c * up) return 0;
  return 1;
}
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]), step = argc > 3 ? atoll(argv[3]) : 1;
  ll tot = 0, bad = 0;
  for (ll N = N1; N <= N2; N += step)
    for (ll u = 3; u * u <= N; u++)
      for (ll up = (3 * N + 2 + 7) / 8; u + 2 * up <= N - 1; up++) {
        if (u == 3 && 2 * up + 4 == N) continue;
        tot++;
        if (!regB(N, u, up)) { bad++; if (bad < 20) printf("BAD N=%lld u=%lld u'=%lld\n", N, u, up); }
      }
  printf("tot %lld bad %lld\n", tot, bad);
  return 0;
}

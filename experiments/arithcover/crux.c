/* crux.c N1 N2 F: the near-boundary pairs u <= sqrt(F*N), delta = N-1-u-2u' < 3u (mixed parity,
   wide, u >= 2, not special): are they all in region B (Theorem B)?  Prints the exceptions. */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
typedef long long ll;
static int special(ll N, ll u, ll up) {
  if (u == 2 && (up == 2 || up == 3)) return 1;
  if (u == 3 && (up == 3 || up == 4)) return 1;
  if (u == 3 && N % 4 == 2 && up == (N - 4) / 2) return 1;
  return 0;
}
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
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  double F = atof(argv[3]);
  ll tot = 0, ex = 0;
  for (ll N = N1; N <= N2; N++)
    for (ll u = 2; (double)u * u <= F * N && 3 * u + 1 <= N; u++)
      for (ll del = 0; del < 3 * u; del++) {
        ll t = N - 1 - u - del;
        if (t % 2) continue;
        ll up = t / 2;
        if (up < u) continue;
        if ((u + N + 1 - up) % 2 != 1 || special(N, u, up)) continue;
        tot++;
        if (!regB(N, u, up)) { ex++; if (u > 2 && ex < 400000) printf("EX N=%lld u=%lld u'=%lld delta=%lld\n", N, u, up, del); }
      }
  printf("tot %lld exceptions %lld\n", tot, ex);
  return 0;
}

/* bz.c N1 N2 DMULT: near-boundary pairs (delta = N-1-u-2u' < DMULT*u ... ) tested with
   orientation B (x = u', y = u), family Z (K = N+2), right index c fixed = floor(u/2):
   exists s in [max(u,2), K/2] with cK - su - 1 in [0, s-1] and aK - su' in [0, s-1], a >= 2.
   Prints failures (u, u', delta) and the largest u(u+delta)/K seen among failures. */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static int witc(ll K, ll x, ll y, ll c) {
  ll lo = y > 2 ? y : 2;
  for (ll s = lo; s <= K / 2; s++) {
    ll Y = c * K - s * y - 1;
    if (Y < 0 || Y > s - 1) continue;
    ll a = (s * x + K - 1) / K, X = a * K - s * x;
    if (X <= s - 1 && a >= 2) return 1;
  }
  return 0;
}
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  double dm = atof(argv[3]);
  ll fails = 0, tot = 0;
  for (ll N = N1; N <= N2; N++) {
    ll K = N + 2;
    for (ll u = 2; 3 * u + 1 <= N; u++)
      for (ll up = u; u + 2 * up <= N - 1; up++) {
        ll del = N - 1 - u - 2 * up;
        if (del >= dm * u) continue;
        if ((u + N + 1 - up) % 2 != 1) continue;
        tot++;
        if (witc(K, up, u, u / 2)) continue;
        fails++;
        if (!(u == 3 && del == 0)) printf("F N=%lld u=%lld u'=%lld delta=%lld  u(u+d)/K=%.3f\n", N, u, up, del,
                                (double)u * (u + del) / K);
      }
  }
  printf("tot %lld fails %lld\n", tot, fails);
  return 0;
}

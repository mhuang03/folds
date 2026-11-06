/* clcost.c N : for the cluster pairs, the number of dirAll calls of `dirAny N u v || dirAny N v u`
   (first success) and the first successful a in each orientation. */
#include "../residual/common.h"
static ll firstA(ll N, ll x, ll y) { for (ll a = 1; a <= x + 1; a++) if (dirAll(N, x, y, a)) return a; return -1; }
int main(int argc, char **argv) {
  ll N = atoll(argv[1]);
  long calls = 0, pts = 0, fails = 0;
  for (ll u = (N - 80) / 4; 4 * u <= N + 40; u++)
    for (ll v = u + 10; u + 2 * v + 1 <= N; v++) {
      if (!(N <= 4 * u + 80 && N <= u + 2 * v + 81 && v + 13 <= 2 * u && (u + (N + 1 - v)) % 2 == 1)) continue;
      pts++;
      ll a1 = firstA(N, u, v), a2 = firstA(N, v, u);
      if (a1 > 0) calls += a1; else if (a2 > 0) calls += u + 1 + a2; else fails++;
      if (pts < 5) printf("u=%lld v=%lld a1=%lld a2=%lld\n", u, v, a1, a2);
    }
  printf("N=%lld pts=%ld calls=%ld avg=%.1f fails=%ld\n", N, pts, calls, (double)calls / pts, fails);
  return 0;
}

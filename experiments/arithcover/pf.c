/* pf.c N1 N2 [verbose]: residual of the POSITION-FREE direct test (union length >= K) over all a,
   combos, orientations; prints residual stats per N (and the residual pairs if verbose). */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static ll mn(ll a, ll b) { return a < b ? a : b; }
static ll mx(ll a, ll b) { return a > b ? a : b; }
static ll nsub(ll a, ll b) { return a > b ? a - b : 0; }
static int okPF(ll K, ll L, ll R, ll al, ll be, ll smax, ll a) {
  ll S2 = mn(nsub(a * K, al) / L, smax);
  ll S1 = mx(mx((nsub(a * K, al) + 1 + L) / (L + 1), R), 2);
  if (S1 > S2) return 0;
  return S1 * R + be + K <= S2 * R + be + S2;
}
static int okEx(ll K, ll L, ll R, ll al, ll be, ll smax, ll a) {
  ll S2 = mn(nsub(a * K, al) / L, smax);
  ll S1 = mx(mx((nsub(a * K, al) + 1 + L) / (L + 1), R), 2);
  if (S1 > S2) return 0;
  ll hi = nsub(S2 * R + be + S2, 1);
  return S1 * R + be <= (hi / K) * K;
}
static int (*ok)(ll, ll, ll, ll, ll, ll, ll);
static int all(ll N, ll x, ll y, ll a) {
  if (a == 1) return y >= 2 && ok(N, x, y - 2, 0, 1, (N + 1) / 2, a);
  if (ok(N + 2, x, y, 0, 1, (N + 2) / 2, a)) return 1;
  if (y >= 2 && ok(N, x, y - 2, 0, 1, (N + 1) / 2, a)) return 1;
  if (y >= 2 && ok(N, x, y - 2, 1, 0, N / 2, a)) return 1;
  return 0;
}
static int any(ll N, ll x, ll y) { for (ll a = 1; a <= x + 1; a++) if (all(N, x, y, a)) return 1; return 0; }
static int special(ll N, ll u, ll up) {
  if (u == 2 && (up == 2 || up == 3)) return 1;
  if (u == 3 && (up == 3 || up == 4)) return 1;
  if (u == 3 && N % 4 == 2 && up == (N - 4) / 2) return 1;
  return 0;
}
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  int verbose = argc > 3 ? atoi(argv[3]) : 0;
  for (ll N = N1; N <= N2; N++) {
    ll tot = 0, res = 0, exfail = 0;
    for (ll u = 2; 3 * u + 1 <= N; u++)
      for (ll up = u; u + 2 * up <= N - 1; up++) {
        ll v = N + 1 - up;
        if ((u + v) % 2 != 1 || special(N, u, up)) continue;
        tot++;
        ok = okPF;
        if (any(N, u, up) || any(N, up, u)) continue;
        res++;
        ok = okEx;
        if (!(any(N, u, up) || any(N, up, u))) exfail++;
        if (verbose) printf("R %lld %lld %lld d=%lld delta=%lld\n", N, u, up, up - u, N - 1 - u - 2 * up);
      }
    printf("N=%lld tot %lld pfres %lld exfail %lld\n", N, tot, res, exfail);
  }
  return 0;
}

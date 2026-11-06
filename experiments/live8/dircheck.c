/* dircheck.c N1 N2: check Live8.ArithCover N for N1 <= N <= N2, faithful to dirOK / dirAll /
   dirAny (Nat semantics): every mixed-parity wide pair (u, v), u + v <= N + 1, u >= 4, passes an
   exact direct test with some a in [2, x + 1] in one of its orientations.  Prints failures and
   per-N counts; also counts, for information, the minimal a used. */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static ll mn(ll a, ll b) { return a < b ? a : b; }
static ll mx(ll a, ll b) { return a > b ? a : b; }
static ll nsub(ll a, ll b) { return a > b ? a - b : 0; }

static int dirOK(ll K, ll L, ll R, ll al, ll be, ll smax, ll a) {
  ll S2 = mn(nsub(a * K, al) / L, smax);
  ll S1 = mx(mx((nsub(a * K, al) + 1 + L) / (L + 1), R), 2);
  if (S1 > S2) return 0;
  ll hi = nsub(S2 * R + be + S2, 1);
  return S1 * R + be <= (hi / K) * K;
}
static int dirAll(ll N, ll x, ll y, ll a) {
  if (dirOK(N + 2, x, y, 0, 1, (N + 2) / 2, a)) return 1;
  if (y >= 2 && dirOK(N, x, y - 2, 0, 1, (N + 1) / 2, a)) return 1;
  if (y >= 2 && dirOK(N, x, y - 2, 1, 0, N / 2, a)) return 1;
  return 0;
}
static int dirAny(ll N, ll x, ll y) {
  for (ll a = 2; a <= x + 1; a++) if (dirAll(N, x, y, a)) return 1;
  return 0;
}

int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  ll bad = 0;
  for (ll N = N1; N <= N2; N++) {
    ll badN = 0;
    for (ll u = 4; 3 * u + 1 <= N; u++)
      for (ll v = mx(2 * u + 2, (N + u + 4) / 2); v <= N + 1 - u; v++) {
        if ((u + v) % 2 != 1) continue;
        ll up = N + 1 - v;
        if (dirAny(N, u, up) || dirAny(N, up, u)) continue;
        badN++;
        if (badN <= 10) printf("FAIL N=%lld u=%lld v=%lld (u'=%lld)\n", N, u, v, up);
      }
    bad += badN;
    if (badN || N % 100 == 0) { printf("N=%lld failures %lld\n", N, badN); fflush(stdout); }
  }
  printf("total failures %lld\n", bad);
  return 0;
}

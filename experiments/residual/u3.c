/* u3.c NMAX: check the explicit witnesses for the family u = 3, N = 3u' + m (m odd, |m| <= 5),
   and for the corner d = 1, delta = 0 (N = 3u', u = u' - 1), for all 301 <= N <= NMAX.
   Templates (PROOFS.txt section 5):
     m = -1, -3, -5: Z, orientation (u', 3), c = 1, s = 3a + t:
        m = -1: t = 0,  a = ceil(M/12);      m = -3: t = -1, a = ceil((u' + 2)/4);
        m = -5: t = -1, a = ceil((3u' + 1)/12)
     m = 1, 3: X(N,s,0), orientation (3, u'), a = 1, s in {u'-2, u'-1, u'} with s = 2 (mod 3), c = (s-2)/3
     m = 5:    the same with s = 0 (mod 3), c = (s - 3)/3
   corner: X(N,s,0), orientation (u', u), a = (u' + 3)/3 (floor), c = a - 1, s = 3a. */
#include "common.h"
static int okWit(ll K, ll x, ll R, ll al, ll be, ll smax, ll amin, ll a, ll c, ll s) {
  if (a < amin || s < 2 || s < R || s > smax) return 0;
  if (s * x + al > a * K || a * K + 1 > s * (x + 1) + al) return 0;
  if (s * R + be > c * K || c * K + 1 > s * R + be + s) return 0;
  return 1;
}
int main(int argc, char **argv) {
  ll NMAX = atoll(argv[1]);
  ll bad = 0, n = 0;
  for (ll N = 301; N <= NMAX; N++) {
    ll M = N + 2;
    for (ll m = -5; m <= 5; m += 2) {
      if ((N - m) % 3) continue;
      ll up = (N - m) / 3;
      int ok;
      if (m < 0) {
        ll a = m == -1 ? (M + 11) / 12 : m == -3 ? (up + 2 + 3) / 4 : (3 * up + 1 + 11) / 12;
        ll t = m == -1 ? 0 : -1;
        ok = okWit(M, up, 3, 0, 1, M / 2, 2, a, 1, 3 * a + t);
      } else {
        ll s = up - 2;
        ll r = m == 5 ? 0 : 2;
        while (((s % 3) + 3) % 3 != r) s++;
        ll c = (s - r - (m == 5 ? 3 : 0)) / 3 + (m == 5 ? 0 : 0);
        if (m == 5) c = (s - 3) / 3; else c = (s - 2) / 3;
        ok = okWit(N, 3, up - 2, 0, 1, (N + 1) / 2, 1, 1, c, s);
      }
      n++;
      if (!ok) { bad++; if (bad < 20) printf("FAIL u3 N=%lld m=%lld u'=%lld\n", N, m, up); }
    }
    if (N % 3 == 0) {
      ll up = N / 3, u = up - 1;
      ll a = (up + 3) / 3;
      int ok = okWit(N, up, u - 2, 0, 1, (N + 1) / 2, 1, a, a - 1, 3 * a);
      n++;
      if (!ok) { bad++; if (bad < 20) printf("FAIL corner N=%lld\n", N); }
    }
  }
  printf("checked %lld, failures %lld\n", n, bad);
  return 0;
}

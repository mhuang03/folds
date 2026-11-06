/* regions.c N1 N2 [verbose]: the polynomial regions proven in Folds/ArithCover.lean.
   B  : orientation (u', u), family Z, c = floor(u/2), two-class slide (PROOFS.txt, Theorem B).
   D  : orientation (u, u'), family Z, a = floor(u/2) (Live8.settled_directZ_region conditions).
   Checks that every pair in B or D passes dirAny (sanity), and counts the residual. */
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
  if (a == 1) return y >= 2 && dirOK(N, x, y - 2, 0, 1, (N + 1) / 2, a);
  if (dirOK(N + 2, x, y, 0, 1, (N + 2) / 2, a)) return 1;
  if (y >= 2 && dirOK(N, x, y - 2, 0, 1, (N + 1) / 2, a)) return 1;
  if (y >= 2 && dirOK(N, x, y - 2, 1, 0, N / 2, a)) return 1;
  return 0;
}
static int dirAny(ll N, ll x, ll y) { for (ll a = 1; a <= x + 1; a++) if (dirAll(N, x, y, a)) return 1; return 0; }
static int special(ll N, ll u, ll up) {
  if (u == 2 && (up == 2 || up == 3)) return 1;
  if (u == 3 && (up == 3 || up == 4)) return 1;
  if (u == 3 && N % 4 == 2 && up == (N - 4) / 2) return 1;
  return 0;
}
/* Theorem B hypotheses */
static int regB(ll N, ll u, ll up) {
  ll M = N + 2, n = M - 2 * up, c = u / 2;
  if (u < 3 || n < 3) return 0;
  if ((u + 1) * (n - 1) > c * M) return 0;                       /* B1 */
  if (u * (u + 1) > c * M) return 0;                             /* B2 */
  if (c * M * (n + 2 * u) < u * ((2 * u + 1) * n - 2 * u) + u * (u + 1) * (2 * n + M - 1)) return 0; /* B3 */
  if (2 * (u + 1) > c * up) return 0;                            /* B4 */
  return 1;
}
/* Region B2: as B but s1 = n - 1 (contiguity is then automatic) */
static int regB2(ll N, ll u, ll up) {
  ll M = N + 2, n = M - 2 * up, c = u / 2;
  if (u < 3 || n < u + 3) return 0;
  if (c * M > (n - 1) * (u + 1)) return 0;                                   /* s1 = n - 1 valid */
  if ((c * M - 2 * u) * n < u * (n * (n - 2) + M + 1)) return 0;            /* length */
  if (2 * M > (n - 1) * up) return 0;                                       /* a >= 2 */
  return 1;
}
static int regD(ll N, ll u, ll up) {
  ll M = N + 2, r = u % 2;
  if (u < 4 || up < u || u + up > N) return 0;
  if ((u - r) * M * (u + up + 1) < 2 * (u + 1) * (M * u + 2 * u * up + u)) return 0;
  if ((u * M - r * M - 2 * u + 2) * (up + 1) < 2 * u * (up * up + M)) return 0;
  return 1;
}
/* Region D0: orientation (u, u'), X(N, s, 0), a = 1 */
static int regD0(ll N, ll u, ll up) {
  ll R = up - 2;
  if (u < 2 || up < u || up < 4 || u + up > N) return 0;
  if (u * (N + 1 + u) * R + u * (u + 1) * N > (u + 1) * (N - u + 1) * (R + 1)) return 0;
  if (u * (R * R + N) > (N - u + 1) * (R + 1)) return 0;
  return 1;
}
/* Region W: orientation (u', u), X(N, s, 0), some a >= 2 with c = a - 1 */
static int regW(ll N, ll u, ll up) {
  ll R = u - 2;
  if (u < 2 || up < u || u + up > N) return 0;
  for (ll a = 2; 2 * a <= up; a++) {
    if (R * (up + 1) > a * N) continue;
    if (2 * up * up + up > a * N + 1 || up > N) continue;
    if ((a * N + up + 1) * R + (up + 1) > (a - 1) * N * (up + 1)) continue;
    if ((a - 1) * N * up > (a * N - up + 1) * (R + 1)) continue;
    return 1;
  }
  return 0;
}
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  int verbose = argc > 3 ? atoi(argv[3]) : 0;
  ll GT = 0, GB = 0, GD = 0, GR = 0, bad = 0;
  for (ll N = N1; N <= N2; N++) {
    ll tot = 0, nb = 0, nd = 0, res = 0;
    for (ll u = 2; 3 * u + 1 <= N; u++)
      for (ll up = u; u + 2 * up <= N - 1; up++) {
        if ((u + N + 1 - up) % 2 != 1 || special(N, u, up)) continue;
        tot++;
        int b = regB(N, u, up) || regB2(N, u, up) || regW(N, u, up), d = regD(N, u, up) || regD0(N, u, up);
        if (b) { nb++; if (!dirAny(N, up, u)) { bad++; printf("BAD-B N=%lld u=%lld u'=%lld\n", N, u, up); } }
        if (d) { nd++; if (!dirAny(N, u, up)) { bad++; printf("BAD-D N=%lld u=%lld u'=%lld\n", N, u, up); } }
        if (!b && !d) {
          res++;
          if (verbose) printf("R N=%lld u=%lld u'=%lld d=%lld delta=%lld\n", N, u, up, up - u, N - 1 - u - 2 * up);
        }
      }
    GT += tot; GB += nb; GD += nd; GR += res;
    if (N % 100 == 0 || N == N2) printf("N=%lld tot %lld B %lld D %lld residual %lld\n", N, tot, nb, nd, res);
  }
  printf("all: tot %lld B %lld D %lld residual %lld bad %lld\n", GT, GB, GD, GR, bad);
  return 0;
}

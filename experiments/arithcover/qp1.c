/* qp1.c N1 N2 JMODE [verbose]: coverage of regions B, D, D' (regions.c) plus the
   position-free Q = P = 1 lemma (orientation (x, y) = (u, u'), family Z, K = M = N + 2, d = y - x):
     fix j >= 1, Delta >= 0, s1 <= s2 with s1 d >= jM - 1 - Delta, s2 d <= jM - 1 + Delta,
     s1 >= max(y, x + 2 Delta, 2), 2 s2 <= M, s1 x >= M + 1 (a >= 2),
     (s2 - s1) x + s2 - 2 Delta >= M.
   JMODE 0: all j; 1: j = floor(d/2) only; 2: j in {floor(d/2), floor(d/2) - 1}.
   Prints the residual counts. */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static ll mn(ll a, ll b) { return a < b ? a : b; }
static ll mx(ll a, ll b) { return a > b ? a : b; }
static ll fdiv(ll a, ll b) { ll q = a / b; if ((a % b != 0) && ((a < 0) != (b < 0))) q--; return q; }
static ll cdiv(ll a, ll b) { return -fdiv(-a, b); }
static int JMODE = 0;
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
static int regD(ll N, ll u, ll up) {
  ll M = N + 2, r = u % 2;
  if (u < 4 || up < u || u + up > N) return 0;
  if ((u - r) * M * (u + up + 1) < 2 * (u + 1) * (M * u + 2 * u * up + u)) return 0;
  if ((u * M - r * M - 2 * u + 2) * (up + 1) < 2 * u * (up * up + M)) return 0;
  return 1;
}
/* D': only the u' branch: a = floor(u/2), aM + 1 <= u'(u+1), and hB */
static int regD2(ll N, ll u, ll up) {
  ll M = N + 2, r = u % 2, a = u / 2;
  if (u < 4 || up < u || u + up > N) return 0;
  if (a * M + 1 > up * (u + 1)) return 0;
  if ((u * M - r * M - 2 * u + 2) * (up + 1) < 2 * u * (up * up + M)) return 0;
  return 1;
}
static int qp1(ll N, ll x, ll y) {
  ll M = N + 2, d = y - x;
  if (d < 1) return 0;
  ll jlo = 1, jhi = d / 2 + 1;
  if (JMODE >= 1) { jlo = d / 2 - (JMODE == 2 ? 1 : 0); jhi = d / 2; }
  for (ll j = mx(jlo, 1); j <= jhi; j++)
    for (ll D = 0; 2 * D <= M; D++) {
      ll s1 = mx(cdiv(j * M - 1 - D, d), mx(y, mx(x + 2 * D, 2)));
      ll s2 = mn(fdiv(j * M - 1 + D, d), M / 2);
      if (s1 > s2 || s1 * x < M + 1) continue;
      if ((s2 - s1) * x + s2 - 2 * D >= M) return 1;
    }
  return 0;
}
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  JMODE = atoi(argv[3]);
  int verbose = argc > 4 ? atoi(argv[4]) : 0;
  ll GT = 0, GR = 0, GR2 = 0;
  for (ll N = N1; N <= N2; N++) {
    ll tot = 0, res = 0, res2 = 0;
    for (ll u = 2; 3 * u + 1 <= N; u++)
      for (ll up = u; u + 2 * up <= N - 1; up++) {
        if ((u + N + 1 - up) % 2 != 1 || special(N, u, up)) continue;
        tot++;
        if (regB(N, u, up) || regD(N, u, up) || regD2(N, u, up)) continue;
        res++;
        if (qp1(N, u, up)) continue;
        res2++;
        if (verbose) printf("R N=%lld u=%lld u'=%lld d=%lld delta=%lld\n", N, u, up, up - u, N - 1 - u - 2 * up);
      }
    GT += tot; GR += res; GR2 += res2;
    printf("N=%lld tot %lld after BDD' %lld after QP1 %lld\n", N, tot, res, res2);
  }
  printf("all: tot %lld BDD' %lld QP1 %lld\n", GT, GR, GR2);
  return 0;
}

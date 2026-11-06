/* rot2.c N1 N2 QMAX mode [LIM]: sliding-window certificates with a fixed linear relation.
   Combo (K, L, R, alpha, beta, smax):  X = aK - sL - alpha in [0, s-1],  Y = cK - sR - beta in [0, s-1].
   direct (fix a), and for coprime 1 <= Q, P <= QMAX the (Q,P)-lemma:
     fix j = Qc - Pa; D(s) = QY - PX = jK - s(QR - PL) - (Q beta - P alpha); |D(s)| <= Delta on [s1, s2];
     X in W(s) = [ceil(Delta/P), min(s-1, floor((Q(s-1) - Delta)/P))], contiguous if |W(s)| >= L;
     a = a* mod Q (a* = -j P^{-1} mod Q); union U = [s1 L + alpha + lo, s2 L + alpha + hi(s2)] must
     contain some aK with a = a* mod Q: mode 0 = |U| >= QK (position-free), mode 1 = exact.
   Prints uncovered pairs. */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static ll fdiv(ll a, ll b) { ll q = a / b; if ((a % b != 0) && ((a < 0) != (b < 0))) q--; return q; }
static ll cdiv(ll a, ll b) { return -fdiv(-a, b); }
static ll fmodp(ll a, ll b) { ll r = a % b; return r < 0 ? r + b : r; }
static int mode = 0, QMAX = 1;
static ll LIM = 60;
static ll gcd(ll a, ll b) { while (b) { ll t = a % b; a = b; b = t; } return a < 0 ? -a : a; }
static ll inv(ll x, ll m) { /* inverse of x mod m, m >= 1 */
  if (m == 1) return 0;
  for (ll i = 1; i < m; i++) if (fmodp(x * i, m) == 1) return i;
  return -1;
}
static int hitLen(ll lo, ll hi, ll K) { return hi >= lo && hi - lo + 1 >= K; }

static int direct(ll K, ll L, ll R, ll al, ll be, ll smax) {
  for (ll a = 1; a * K <= (smax + 1) * (L + 1) + al + K; a++) {
    ll S1 = cdiv(a * K - al + 1, L + 1), S2 = fdiv(a * K - al, L);
    if (S1 < R) S1 = R;
    if (S1 < 2) S1 = 2;
    if (S2 > smax) S2 = smax;
    if (S1 > S2) continue;
    ll lo = S1 * R + be, hi = S2 * R + be + S2 - 1;
    if (mode == 0 ? hitLen(lo, hi, K) : (hi >= lo && fdiv(hi, K) * K >= lo)) return 1;
  }
  return 0;
}

static int qp(ll K, ll L, ll R, ll al, ll be, ll smax, ll Q, ll P) {
  ll E = Q * R - P * L, C = Q * be - P * al;
  ll pinv = inv(P, Q);
  /* j range: s0 = (jK - C)/E in [L, smax + K] */
  ll jlo, jhi;
  if (E == 0) { jlo = jhi = fdiv(C, K); jhi = jlo + 1; }
  else {
    ll A = cdiv(L * E + C, K), B = fdiv((smax + 1) * E + C, K);
    if (E > 0) { jlo = A - 1; jhi = B + 1; } else { jlo = B - 1; jhi = A + 1; }
  }
  for (ll j = jlo; j <= jhi; j++) {
    ll astar = fmodp(-j * pinv, Q);
    for (int dd = 1; dd <= 12; dd++) {
      ll Delta = (smax * dd) / 24;
      /* s range with |jK - sE - C| <= Delta */
      ll s1, s2;
      if (E > 0) { s1 = cdiv(j * K - C - Delta, E); s2 = fdiv(j * K - C + Delta, E); }
      else if (E < 0) { s1 = cdiv(j * K - C + Delta, E); s2 = fdiv(j * K - C - Delta, E); }
      else { if (j * K - C > Delta || j * K - C < -Delta) continue; s1 = 2; s2 = smax; }
      if (s2 > smax) s2 = smax;
      if (s1 < 2) s1 = 2;
      ll lo = cdiv(Delta, P);
      /* contiguity: |W(s)| >= L for s in [s1, s2 - 1]; hi(s) nondecreasing */
      while (s1 <= s2) {
        ll hi = s1 - 1, h2 = fdiv(Q * (s1 - 1) - Delta, P);
        if (h2 < hi) hi = h2;
        if (hi - lo + 1 >= L) break;
        s1++;
      }
      if (s1 > s2) continue;
      ll hi2 = s2 - 1, h2 = fdiv(Q * (s2 - 1) - Delta, P);
      if (h2 < hi2) hi2 = h2;
      ll ulo = s1 * L + al + lo, uhi = s2 * L + al + hi2;
      if (uhi < ulo) continue;
      if (mode == 0) { if (uhi - ulo + 1 >= Q * K) return 1; }
      else {
        /* exists a = astar mod Q with aK in [ulo, uhi] */
        ll a = cdiv(ulo, K);
        a += fmodp(astar - a, Q);
        if (a * K <= uhi) return 1;
      }
    }
  }
  return 0;
}

static int combo(ll K, ll L, ll R, ll al, ll be, ll smax) {
  if (L < 1 || R < 1) return 0;
  if (direct(K, L, R, al, be, smax)) return 1;
  for (ll Q = 1; Q <= QMAX; Q++)
    for (ll P = fdiv(Q * R, L); P <= fdiv(Q * R, L) + 1; P++) {
      if (P < 1 || gcd(Q, P) != 1) continue;
      if (qp(K, L, R, al, be, smax, Q, P)) return 1;
    }
  return 0;
}

int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  QMAX = atoi(argv[3]);
  mode = atoi(argv[4]);
  if (argc > 5) LIM = atoll(argv[5]);
  ll unc = 0, tot = 0;
  for (ll N = N1; N <= N2; N++) {
    ll M = N + 2;
    for (ll u = 1; 3 * u + 1 <= N; u++)
      for (ll up = u; u + 2 * up <= N - 1; up++) {
        ll v = N + 1 - up;
        if ((u + v) % 2 == 0) continue;
        if (u == 1 && up == 1) continue;
        if (u == 3 && up == 4) continue;
        if (u == 1 && N % 4 == 0 && up == N / 2 - 1) continue;
        tot++;
        int ok = 0;
        for (int o = 0; o < 2 && !ok; o++) {
          ll x = o ? up : u, y = o ? u : up;
          ok = combo(M, x, y, 0, 1, M / 2) || combo(N, x, y - 2, 0, 1, (N + 1) / 2) ||
               combo(N, x, y - 2, 1, 0, N / 2);
        }
        if (!ok) { unc++; if (unc <= LIM) printf("UNC N=%lld u=%lld u'=%lld\n", N, u, up); }
      }
  }
  printf("total %lld uncovered %lld\n", tot, unc);
  return 0;
}

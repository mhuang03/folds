/* rot.c N1 N2 [mode]: position-free sliding-window (rotation) certificates for wide mixed pairs.
   For combo (K, L, R, alpha, beta, smax):
     (I)  aK - sL in [alpha, alpha + s - 1]     (II) cK - sR in [beta, beta + s - 1]
   direct(a):  s in I_a = [S1, S2] (where (I) holds), S1 >= R (contiguous windows of (II));
               union = [S1 R + beta, S2 R + beta + S2 - 1]; success if its length >= K.
   diff(k, Delta): E = R - L, D(s) = kK - sE - (beta - alpha); s in [s1, s2] with |D(s)| <= Delta,
               s >= L + 2 Delta; windows [sL + alpha + Delta, sL + alpha + s - 1 - Delta];
               union = [s1 L + alpha + Delta, s2 L + alpha + s2 - 1 - Delta]; success if length >= K.
   mode 0: position-free (length >= K); mode 1: union contains a multiple of K.
   Prints uncovered pairs (u, u'), and counts. */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static ll fdiv(ll a, ll b) { ll q = a / b; if ((a % b != 0) && ((a < 0) != (b < 0))) q--; return q; }
static ll cdiv(ll a, ll b) { return -fdiv(-a, b); }
static int mode = 0;
static ll LIM = 60;

static int good(ll lo, ll hi, ll K) {
  if (hi < lo) return 0;
  if (mode == 0) return hi - lo + 1 >= K;
  return fdiv(hi, K) * K >= lo;
}

/* returns 1 if a certificate exists */
static int combo(ll K, ll L, ll R, ll al, ll be, ll smax) {
  if (L < 1 || R < 1) return 0;
  /* direct */
  for (ll a = 1; a * K <= (smax + 1) * (L + 1) + al + K; a++) {
    ll S1 = cdiv(a * K - al + 1, L + 1), S2 = fdiv(a * K - al, L);
    if (S1 < R) S1 = R;
    if (S1 < 2) S1 = 2;
    if (S2 > smax) S2 = smax;
    if (S1 > S2) continue;
    if (good(S1 * R + be, S2 * R + be + S2 - 1, K)) return 1;
  }
  /* diff */
  ll E = R - L;
  if (E != 0) {
    ll kmax = (smax * (E > 0 ? E : -E)) / K + 2;
    for (ll k = -kmax; k <= kmax; k++) {
      /* D(s) = k K - s E - (be - al); choose Delta from a small set of fractions */
      for (int dd = 1; dd <= 8; dd++) {
        ll s0 = fdiv(k * K - (be - al), E); /* D(s0) ~ 0 */
        ll Delta = (s0 > L ? (s0 - L) * dd / 16 : 0);
        if (Delta < 0) continue;
        /* s range: |kK - sE - (be-al)| <= Delta */
        ll s1, s2;
        if (E > 0) { s1 = cdiv(k * K - (be - al) - Delta, E); s2 = fdiv(k * K - (be - al) + Delta, E); }
        else { s1 = cdiv(k * K - (be - al) + Delta, E); s2 = fdiv(k * K - (be - al) - Delta, E); }
        if (s1 < L + 2 * Delta) s1 = L + 2 * Delta;
        if (s1 < 2) s1 = 2;
        if (s2 > smax) s2 = smax;
        if (s1 > s2) continue;
        if (good(s1 * L + al + Delta, s2 * L + al + s2 - 1 - Delta, K)) return 1;
      }
    }
  }
  return 0;
}

int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  if (argc > 3) mode = atoi(argv[3]);
  if (argc > 4) LIM = atoll(argv[4]);
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
          ok = combo(M, x, y, 0, 1, M / 2) ||            /* Z */
               combo(N, x, y - 2, 0, 1, (N + 1) / 2) ||  /* X0 */
               combo(N, x, y - 2, 1, 0, N / 2);          /* X1 */
        }
        if (!ok) { unc++; if (unc <= LIM) printf("UNC N=%lld u=%lld u'=%lld\n", N, u, up); }
      }
  }
  printf("total %lld uncovered %lld\n", tot, unc);
  return 0;
}

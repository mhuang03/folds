/* qslide.c N1 N2 QMAX MODE [verbose]: coverage of the "class slide" lemmas (faithful: s >= R).
   Combo (K, L = x, R, al, be, smax, amin).  Witness: s in [max(R,2), smax],
     aK - sL - al in [0, s-1] (a >= amin),  cK - sR - be in [0, s-1].
   Rule D(a): direct (fix a), union of the R-windows.                         (= dirOK)
   Rule FC(c; p/q): fix c (s in J_c), approximate L by pK/q: n = pK - qL, t = sp - qa;
     q(aK - sL - al) = sn - tK - q al, so the x-condition is tK in W(s) = [sn - q al - q(s-1), sn - q al]
     with t = sp (mod q).  For each class r mod q the windows over s = r (mod q) must be
     consecutive-overlapping; their unions U_r; if gcd(p,q) = 1 and the common part of the U_r
     contains a multiple of K, some class works.  (a >= amin checked crudely: a = (sp - t)/q.)
   Rule FA(a; p/q): fix a (s in I_a), approximate R by pK/q (the y-condition likewise).
   MODE 0: position-free (common part has length >= K); MODE 1: exact (contains a multiple).
   Prints per-N residual counts (pairs failing all rules); verbose prints residual pairs. */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static int MODE = 0, QMAX = 2;
static ll fdiv(ll a, ll b) { ll q = a / b; if ((a % b != 0) && ((a < 0) != (b < 0))) q--; return q; }
static ll cdiv(ll a, ll b) { return -fdiv(-a, b); }
static ll gcd(ll a, ll b) { if (a < 0) a = -a; if (b < 0) b = -b; while (b) { ll t = a % b; a = b; b = t; } return a; }
static ll mx(ll a, ll b) { return a > b ? a : b; }
static ll mn(ll a, ll b) { return a < b ? a : b; }

static int hit(ll lo, ll hi, ll K) {
  if (hi < lo) return 0;
  if (MODE == 0) return hi - lo + 1 >= K;
  return fdiv(hi, K) * K >= lo;
}

/* class slide over s in [S1, S2]; windows W(s) = [s n - q g - q(s-1), s n - q g] */
static int classSlide(ll K, ll S1, ll S2, ll n, ll q, ll g) {
  if (S2 - S1 + 1 < q) return 0;
  ll clo = -(1LL << 62), chi = (1LL << 62);
  for (ll r = 0; r < q; r++) {
    ll s0 = S1 + r, ulo = 1LL << 62, uhi = -(1LL << 62);
    ll plo = 0, phi = 0;
    for (ll s = s0; s <= S2; s += q) {
      ll lo = s * n - q * g - q * (s - 1), hi = s * n - q * g;
      if (s > s0 && (lo > phi + 1 || plo > hi + 1)) return 0; /* not contiguous */
      plo = lo; phi = hi;
      ulo = mn(ulo, lo); uhi = mx(uhi, hi);
    }
    clo = mx(clo, ulo); chi = mn(chi, uhi);
  }
  return hit(clo, chi, K);
}

static int combo(ll K, ll L, ll R, ll al, ll be, ll smax, ll amin) {
  if (L < 1 || R < 0) return 0;
  ll Rlo = mx(R, 2);
  /* D(a) */
  for (ll a = amin; a <= L + 1; a++) {
    ll S2 = mn(fdiv(a * K - al, L), smax), S1 = mx(cdiv(a * K - al + 1, L + 1), Rlo);
    if (S1 > S2) continue;
    if (hit(S1 * R + be, S2 * R + be + S2 - 1, K)) return 1;
  }
  for (ll q = 1; q <= QMAX; q++) {
    /* FC(c; p/q) */
    for (ll c = 1; c * K <= (smax + 1) * (R + 1) + K; c++) {
      ll S1 = mx(cdiv(c * K - be + 1, R + 1), Rlo), S2 = R > 0 ? mn(fdiv(c * K - be, R), smax) : smax;
      if (S1 > S2) continue;
      ll p0 = fdiv(q * L, K);
      for (ll p = p0; p <= p0 + 1; p++) {
        if (gcd(p, q) != 1) continue;
        if (q == 1 && p == 0) continue;
        ll n = p * K - q * L;
        /* a >= amin: a = (sp - t)/q with tK <= sn - q al  => a >= (sL + al)/K roughly; need S1*L >= (amin-1)K */
        if (S1 * L + al <= (amin - 1) * K) continue;
        if (classSlide(K, S1, S2, n, q, al)) return 1;
      }
    }
    /* FA(a; p/q) */
    for (ll a = amin; a <= L + 1; a++) {
      ll S2 = mn(fdiv(a * K - al, L), smax), S1 = mx(cdiv(a * K - al + 1, L + 1), Rlo);
      if (S1 > S2) continue;
      ll p0 = fdiv(q * R, K);
      for (ll p = p0; p <= p0 + 1; p++) {
        if (gcd(p, q) != 1) continue;
        if (q == 1 && p == 0) continue; /* that is D(a) */
        ll n = p * K - q * R;
        if (classSlide(K, S1, S2, n, q, be)) return 1;
      }
    }
  }
  return 0;
}
static int special(ll N, ll u, ll up) {
  if (u == 2 && (up == 2 || up == 3)) return 1;
  if (u == 3 && (up == 3 || up == 4)) return 1;
  if (u == 3 && N % 4 == 2 && up == (N - 4) / 2) return 1;
  return 0;
}
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  QMAX = atoi(argv[3]); MODE = atoi(argv[4]);
  int verbose = argc > 5 ? atoi(argv[5]) : 0;
  ll gt = 0, gr = 0;
  for (ll N = N1; N <= N2; N++) {
    ll M = N + 2, tot = 0, res = 0;
    for (ll u = 2; 3 * u + 1 <= N; u++)
      for (ll up = u; u + 2 * up <= N - 1; up++) {
        if ((u + N + 1 - up) % 2 != 1 || special(N, u, up)) continue;
        tot++;
        int ok = 0;
        for (int o = 0; o < 2 && !ok; o++) {
          ll x = o ? up : u, y = o ? u : up;
          ok = combo(M, x, y, 0, 1, M / 2, 2) || (y >= 2 && combo(N, x, y - 2, 0, 1, (N + 1) / 2, 1)) ||
               (y >= 2 && combo(N, x, y - 2, 1, 0, N / 2, 2));
        }
        if (!ok) {
          res++;
          if (verbose) printf("R N=%lld u=%lld u'=%lld d=%lld delta=%lld\n", N, u, up, up - u, N - 1 - u - 2 * up);
        }
      }
    gt += tot; gr += res;
    if (verbose || N == N2 || N % 50 == 0) printf("N=%lld tot %lld residual %lld\n", N, tot, res);
  }
  printf("all: tot %lld residual %lld\n", gt, gr);
  return 0;
}

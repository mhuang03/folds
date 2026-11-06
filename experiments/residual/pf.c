/* pf.c N1 N2 QMAX [verbose]: lattice-direction (parallelogram) test on the residual of the old regions.
   Pi = {(a, c) real : the nine "length >= 1" conditions of pi.h} (linear in (a, c)).
   For a primitive direction v = (p, q) (a-step p, c-step q) with complement w (p q' - p' q = 1),
   the lattice lines are nu*w + t*v, nu integer.  len(nu) = length in t of the chord of Pi.
   PF(v): {nu real : len(nu) >= 1} has length >= 1  (position-free: some integer nu works,
          and then some integer t).
   EX(v): some integer nu with len(nu) >= 1 (exact for this direction).
   Reports the residual of PF and EX over all combos and all v with 0 <= q <= QMAX, |p| <= 3 QMAX. */
#include "pi.h"
#include <math.h>
typedef struct { double A, C, D; } Lin;
static int nlin;
static Lin lin[12];
static void addc(double A, double C, double D) { lin[nlin].A = A; lin[nlin].C = C; lin[nlin].D = D; nlin++; }
static void buildPi(ll K, ll L, ll R, ll al, ll be, ll smax, ll amin) {
  nlin = 0;
  ll R2 = R > 2 ? R : 2;
  addc(K, 0, -al - L * (L + 2));
  addc((double)K * (R + 1), -(double)K * L, -al * (R + 1) + be * L - L - L * (R + 1));
  addc(K, 0, -al - L * (R2 + 1));
  if (R >= 1) {
    addc(-(double)K * R, (double)K * (L + 1), -be * (L + 1) + al * R - R - R * (L + 1));
    addc(0, K, -be - R * (R + 2));
    addc(0, K, -be - R * (R2 + 1));
  }
  addc(-K, 0, al + smax * (L + 1) - L - 2);
  addc(0, -K, be + smax * (R + 1) - R - 2);
  addc(1, 0, -amin);
  addc(0, 1, -1);
}
static ll egcd(ll a, ll b, ll *x, ll *y) {
  if (b == 0) { *x = (a >= 0 ? 1 : -1); *y = 0; return a >= 0 ? a : -a; }
  ll x1, y1, g = egcd(b, a % b, &x1, &y1);
  *x = y1; *y = x1 - (a / b) * y1;
  return g;
}
static double P_, Q_, P2_, Q2_;
static double chord(double nu) {
  double lo = -1e18, hi = 1e18;
  for (int i = 0; i < nlin; i++) {
    double g = lin[i].A * P_ + lin[i].C * Q_;
    double h = lin[i].A * P2_ + lin[i].C * Q2_;
    double r = nu * h + lin[i].D; /* g t + r >= 0 */
    if (fabs(g) < 1e-12) { if (r < -1e-9) return -1e18; continue; }
    double t = -r / g;
    if (g > 0) { if (t > lo) lo = t; } else { if (t < hi) hi = t; }
  }
  return hi - lo;
}
/* returns 2 if PF, 1 if EX only, 0 otherwise */
static int testDir(ll p, ll q) {
  ll x, y;
  /* need p q' - p' q = 1 : egcd on (p, q): p*X + q*Y = 1 -> q' = X, p' = -Y */
  ll g = egcd(p, q, &x, &y);
  if (g != 1) return 0;
  P_ = p; Q_ = q; Q2_ = x; P2_ = -y;
  /* find nu range: scan to find max of concave chord */
  double lo = -1e7, hi = 1e7;
  for (int it = 0; it < 200; it++) {
    double m1 = lo + (hi - lo) / 3, m2 = hi - (hi - lo) / 3;
    if (chord(m1) < chord(m2)) lo = m1; else hi = m2;
  }
  double nm = (lo + hi) / 2;
  if (chord(nm) < 1) return 0;
  /* left end */
  double a = nm - 1e7, b = nm;
  for (int it = 0; it < 200; it++) { double m = (a + b) / 2; if (chord(m) >= 1) b = m; else a = m; }
  double left = b;
  a = nm; b = nm + 1e7;
  for (int it = 0; it < 200; it++) { double m = (a + b) / 2; if (chord(m) >= 1) a = m; else b = m; }
  double right = a;
  if (right - left >= 1 + 1e-9) return 2;
  if (floor(right) >= left - 1e-9) return 1;
  return 0;
}
static int QMAX = 6;
static int testPair(ll N, ll u, ll up, int *bq) {
  int best = 0;
  for (int o = 0; o < 2; o++) {
    ll x = o ? up : u, y = o ? u : up;
    for (int f = 0; f < 3; f++) {
      ll K, R, al, be, smax, amin;
      if (f > 0 && y < 2) continue;
      comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
      buildPi(K, x, R, al, be, smax, amin);
      for (ll q = 0; q <= QMAX; q++)
        for (ll p = (q == 0 ? 1 : 0); p <= (q == 0 ? 1 : 3 * q + 3); p++) {
          int r = testDir(p, q);
          if (r > best) { best = r; *bq = (int)q; }
          if (best == 2) return 2;
        }
    }
  }
  return best;
}
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  QMAX = atoi(argv[3]);
  int verbose = argc > 4 ? atoi(argv[4]) : 0;
  for (ll N = N1; N <= N2; N++) {
    ll tot = 0, res = 0, npf = 0, nex = 0;
    ll hq[64] = {0};
    for (ll u = 2; 3 * u + 1 <= N; u++)
      for (ll up = u; u + 2 * up <= N - 1; up++) {
        if (!isPair(N, u, up)) continue;
        tot++;
        if (provenOld(N, u, up)) continue;
        res++;
        int bq = -1;
        int r = testPair(N, u, up, &bq);
        if (r == 2) { npf++; hq[bq]++; }
        if (r >= 1) nex++;
        if (verbose && r < 2) printf("%s N=%lld u=%lld u'=%lld d=%lld delta=%lld\n", r ? "EX" : "NO", N, u, up, up - u, N - 1 - u - 2 * up);
      }
    printf("N=%lld tot %lld res %lld PF %lld EX %lld   q:", N, tot, res, npf, nex);
    for (int q = 0; q <= QMAX; q++) printf(" %lld", hq[q]);
    printf("\n");
  }
  return 0;
}

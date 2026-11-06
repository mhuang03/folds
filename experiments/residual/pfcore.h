#include "pi.h"
#ifndef PFCORE_H
#define PFCORE_H
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
#endif

/* cert.c N u u' : a RegionPF or RegionSL certificate for one pair (family f, orientation o,
   slice (p, j), corner P, shear delta, sides w1, w2), printed with rationals of denominator
   1000 (used to test the Lean definitions on examples). */
#include "slice.h"
#include <math.h>
static int printCert(ll p, ll q) {
  ll xx, yy;
  egcd2(p, q, &xx, &yy);
  ll p2 = -yy, q2 = xx;
  double lo = -1e30, hi = 1e30;
  LL g1[16], g2[16];
  for (int i = 0; i < ng; i++) { g1[i] = gs[i].A * p + gs[i].C * q; g2[i] = gs[i].A * p2 + gs[i].C * q2; }
  for (int i = 0; i < ng; i++) for (int k = 0; k < ng; k++) {
    if (!(g1[i] > 0 && g1[k] < 0)) continue;
    double a1 = (double)g1[i], b1 = -(double)g1[k];
    double E = a1 * (double)g2[k] + b1 * (double)g2[i], F = a1 * b1 - a1 * (double)gs[k].D - b1 * (double)gs[i].D;
    if (E > 0) { if (F / E > lo) lo = F / E; } else if (E < 0) { if (F / E < hi) hi = F / E; }
  }
  for (int i = 0; i < ng; i++) if (g1[i] == 0 && g2[i] != 0) {
    double v = -(double)gs[i].D / (double)g2[i];
    if (g2[i] > 0) { if (v > lo) lo = v; } else { if (v < hi) hi = v; }
  }
  double nu0 = (lo + hi - 1) / 2;
  long nn = (long)floor(nu0 * 1000);
  double nus[2] = {nn / 1000.0, nn / 1000.0 + 1};
  double tl[2];
  for (int z = 0; z < 2; z++) {
    double L0 = -1e30, U0 = 1e30;
    for (int i = 0; i < ng; i++) {
      double r = nus[z] * (double)g2[i] + (double)gs[i].D;
      if (g1[i] > 0) { double t = -r / (double)g1[i]; if (t > L0) L0 = t; }
      else if (g1[i] < 0) { double t = r / -(double)g1[i]; if (t < U0) U0 = t; }
    }
    tl[z] = (L0 + U0 - 1) / 2;
  }
  long t0 = (long)floor(tl[0] * 1000), t1 = (long)floor(tl[1] * 1000);
  printf("w1=(%lld,%lld) w2=(%lld,%lld)\n", p, q, p2, q2);
  printf("P = (%lld/1000, %lld/1000), delta = %lld/1000\n", nn * p2 + t0 * p, nn * q2 + t0 * q, (ll)(t1 - t0));
  return 1;
}
int main(int argc, char **argv) {
  ll N = atoll(argv[1]), u = atoll(argv[2]), up = atoll(argv[3]);
  for (int o = 1; o >= 0; o--) {
    ll x = o ? up : u, y = o ? u : up;
    for (int f = 0; f < 3; f++) {
      if (f > 0 && y < 3) continue;
      ll K, R, al, be, smax, amin;
      comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
      buildCons(K, x, R, al, be, smax, amin);
      for (ll q = 0; q <= 4; q++)
        for (ll p = (q == 0 ? 1 : 0); p <= (q == 0 ? 1 : 3 * q + 3); p++)
          if (parOKdir(p, q)) { printf("PF o=%d f=%d\n", o, f); return !printCert(p, q); }
    }
  }
  for (int o = 1; o >= 0; o--) {
    ll x = o ? up : u, y = o ? u : up;
    for (int f = 0; f < 3; f++) {
      if (f > 0 && y < 3) continue;
      ll K, R, al, be, smax, amin;
      comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
      for (ll p = 0; p <= 3; p++) {
        ll jlo = -(p * smax * (R + 1)) / K - 2, jhi = (smax * (x + 1)) / K + 2;
        for (ll j = jlo; j <= jhi; j++) {
          buildSlice(K, x, R, al, be, smax, amin, p, j);
          for (ll k = 0; k <= SLQ; k++)
            for (ll sg = (k == 0 ? 1 : 0); sg <= (k == 0 ? 1 : SLS); sg++)
              if (parOKdir(sg, k)) { printf("SL o=%d f=%d p=%lld j=%lld\n", o, f, p, j); return !printCert(sg, k); }
        }
      }
    }
  }
  printf("none\n");
  return 1;
}

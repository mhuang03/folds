/* nuint.h: the exact nu-interval of parok.h for a direction w1 = (p1, q1): returns 1 and
   lo = loN/loD, hi = hiN/hiD (nu in [lo, hi] <=> chord(nu) >= 1), and which constraint pairs
   (i, k) define lo and hi (k = -1: a single constraint with g1 = 0).  w2 = (p2, q2) as parok.h. */
#ifndef NUINT_H
#define NUINT_H
#include "../residual/parok.h"
typedef struct { LL loN, loD, hiN, hiD; int li, lk, hi_i, hk; ll p2, q2; int ok; } NuI;
static NuI nuInterval(ll p1, ll q1) {
  NuI r; r.ok = 0;
  ll x, y;
  if (egcd2(p1, q1, &x, &y) != 1) return r;
  ll p2 = -y, q2 = x; r.p2 = p2; r.q2 = q2;
  LL g1[16], g2[16];
  for (int i = 0; i < ng; i++) { g1[i] = gs[i].A * p1 + gs[i].C * q1; g2[i] = gs[i].A * p2 + gs[i].C * q2; }
  int haveLo = 0, haveHi = 0;
  LL loN = 0, loD = 1, hiN = 0, hiD = 1;
  int empty = 0;
#define ADDC2(E, F, I, K) do { LL e_ = (E), f_ = (F); \
    if (e_ == 0) { if (f_ > 0) empty = 1; } \
    else if (e_ > 0) { if (!haveLo || fcmp(f_, e_, loN, loD) > 0) { loN = f_; loD = e_; haveLo = 1; r.li = I; r.lk = K; } } \
    else { if (!haveHi || fcmp(-f_, -e_, hiN, hiD) < 0) { hiN = -f_; hiD = -e_; haveHi = 1; r.hi_i = I; r.hk = K; } } } while (0)
  for (int i = 0; i < ng; i++) if (g1[i] == 0) ADDC2(g2[i], -gs[i].D, i, -1);
  for (int i = 0; i < ng; i++) {
    if (g1[i] <= 0) continue;
    for (int k = 0; k < ng; k++) {
      if (g1[k] >= 0) continue;
      LL a1 = g1[i], b1 = -g1[k];
      ADDC2(a1 * g2[k] + b1 * g2[i], a1 * b1 - a1 * gs[k].D - b1 * gs[i].D, i, k);
    }
  }
  if (!haveLo || !haveHi || empty) return r;
  r.loN = loN; r.loD = loD; r.hiN = hiN; r.hiD = hiD; r.ok = 1;
  return r;
}
static double nuLen(NuI r) { return r.ok ? (double)r.hiN / (double)r.hiD - (double)r.loN / (double)r.loD : -1e9; }
#endif

/* parok.h: exact test of Lean's `ParOK (famCons K L R al be smax amin)` for a given lattice
   direction w1 = (p1, q1) (a-step, c-step).  The 13 constraints of `famCons` are scaled to integer
   linear forms g(a, c) = A a + C c + D >= 0 (multiplied by the positive denominators).
   Parametrising (a, c) = nu * w2 + t * w1 (w2 an integer complement, det(w1, w2) = 1), ParOK with
   side w1 holds iff {nu real : chord(nu) >= 1 in t} has length >= 1 (then take the corners
   (nu0, t0), (nu0, t0 + 1), (nu0 + 1, t1), (nu0 + 1, t1 + 1), delta = t1 - t0).
   Exact in __int128 (fine for N <= ~10^4). */
#ifndef PAROK_H
#define PAROK_H
#include "common.h"
typedef __int128 LL;
typedef struct { LL A, C, D; } G;
typedef struct { LL A, C, D, den; } Q; /* (A a + C c + D) / den */
static int ng;
static G gs[16];
static void gap(Q u, Q l) { /* u - l - 1 >= 0, times u.den * l.den */
  gs[ng].A = l.den * u.A - u.den * l.A;
  gs[ng].C = l.den * u.C - u.den * l.C;
  gs[ng].D = l.den * u.D - u.den * l.D - u.den * l.den;
  ng++;
}
static void buildCons(ll K, ll L, ll R, ll al, ll be, ll smax, ll amin) {
  Q U1 = {K, 0, -al, L}, U2 = {0, K, -be, R}, U3 = {0, 0, smax, 1};
  Q L1 = {K, 0, 1 - al, L + 1}, L2 = {0, K, 1 - be, R + 1}, L3 = {0, 0, R, 1}, L4 = {0, 0, 2, 1};
  Q Us[3] = {U1, U2, U3}, Ls[4] = {L1, L2, L3, L4};
  ng = 0;
  for (int i = 0; i < 3; i++) for (int j = 0; j < 4; j++) gap(Us[i], Ls[j]);
  gs[ng].A = 1; gs[ng].C = 0; gs[ng].D = -amin; ng++;
}
static ll egcd2(ll a, ll b, ll *x, ll *y) {
  if (b == 0) { *x = (a >= 0 ? 1 : -1); *y = 0; return a >= 0 ? a : -a; }
  ll x1, y1, g = egcd2(b, a % b, &x1, &y1);
  *x = y1; *y = x1 - (a / b) * y1;
  return g;
}
/* compare fractions n1/d1 vs n2/d2 (d > 0) : returns sign of n1/d1 - n2/d2 */
static int fcmp(LL n1, LL d1, LL n2, LL d2) { LL l = n1 * d2, r = n2 * d1; return l < r ? -1 : (l > r); }
/* ParOK with side w1 = (p1, q1) */
static int parOKdir(ll p1, ll q1) {
  ll x, y;
  if (egcd2(p1, q1, &x, &y) != 1) return 0;
  /* p1 x + q1 y = 1 ; want p1 q2 - p2 q1 = 1 : q2 = x, p2 = -y */
  ll p2 = -y, q2 = x;
  LL g1[16], g2[16];
  for (int i = 0; i < ng; i++) { g1[i] = gs[i].A * p1 + gs[i].C * q1; g2[i] = gs[i].A * p2 + gs[i].C * q2; }
  /* constraints on nu:  E nu >= F  */
  int haveLo = 0, haveHi = 0;
  LL loN = 0, loD = 1, hiN = 0, hiD = 1; /* nu >= loN/loD, nu <= hiN/hiD */
#define ADDC(E, F) do { LL e_ = (E), f_ = (F); \
    if (e_ == 0) { if (f_ > 0) return 0; } \
    else if (e_ > 0) { if (!haveLo || fcmp(f_, e_, loN, loD) > 0) { loN = f_; loD = e_; haveLo = 1; } } \
    else { if (!haveHi || fcmp(-f_, -e_, hiN, hiD) < 0) { hiN = -f_; hiD = -e_; haveHi = 1; } } } while (0)
  int nlow = 0, nup = 0;
  for (int i = 0; i < ng; i++) {
    if (g1[i] == 0) { ADDC(g2[i], -gs[i].D); continue; }
    if (g1[i] > 0) nlow++; else nup++;
  }
  if (!nlow || !nup) return 0; /* unbounded chord: should not happen */
  for (int i = 0; i < ng; i++) {
    if (g1[i] <= 0) continue;
    for (int k = 0; k < ng; k++) {
      if (g1[k] >= 0) continue;
      LL a1 = g1[i], b1 = -g1[k];
      /* lower_i = -(D_i + nu g2_i)/a1 ; upper_k = (D_k + nu g2_k)/b1 ; upper - lower >= 1 */
      /* a1 (D_k + nu g2_k) + b1 (D_i + nu g2_i) >= a1 b1 */
      ADDC(a1 * g2[k] + b1 * g2[i], a1 * b1 - a1 * gs[k].D - b1 * gs[i].D);
    }
  }
  if (!haveLo || !haveHi) return 0;
  /* hi - lo >= 1 :  hiN/hiD - loN/loD >= 1  */
  return hiN * loD - loN * hiD >= hiD * loD;
}
static int QMAXP = 4;
/* RegionPF for one family/orientation: some direction with q <= QMAXP */
static int parOKany(void) {
  for (ll q = 0; q <= QMAXP; q++)
    for (ll p = (q == 0 ? 1 : 0); p <= (q == 0 ? 1 : 3 * q + 3); p++)
      if (parOKdir(p, q)) return 1;
  return 0;
}
/* Lean RegionPF N u u' (directions limited to q <= QMAXP) ; which = bitmask of successful combos */
static int regionPF(ll N, ll u, ll up) {
  for (int o = 0; o < 2; o++) {
    ll x = o ? up : u, y = o ? u : up;   /* o = 0: orientation (u, u') */
    for (int f = 0; f < 3; f++) {
      if (f > 0 && y < 3) continue;
      ll K, R, al, be, smax, amin;
      comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
      buildCons(K, x, R, al, be, smax, amin);
      if (parOKany()) return 1;
    }
  }
  return 0;
}
#endif

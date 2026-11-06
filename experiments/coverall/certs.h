/* certs.h: explicit ParOK certificates as functions of (N, u, u').
   Generic edge certificate for a family (K, L = x, R, al, be, S = smax) and direction
   w1 = (p, 1), w2 = (p - 1, 1):
   - f4-edge (L + 1 > p(R + 1) - ...: f4 = U2 - L1 - 1 increases along w1): the corners P and
     P + w2 + delta w1 lie on the edge U2 - L1 = 1, parametrised by sigma = L1:
        K a = sigma (L + 1) + al - 1,  K c = (sigma + 1) R + be;
     P on the outer line, sigma1 = min(sigma8, sigma9) (the upper corner P + w1 touches a top),
        sigma8 = S - 1 - K p/(L + 1),  sigma9 = ((S - 1)(R + 1) - K - 1)/R - 1;
     the inner line: sigma3 = sigma1 - K/(L + 1 - pR).
   - f1-edge (f1 = U1 - L2 - 1 increases along w1): corners on U1 - L2 = 1, tau = L2:
        K c = tau (R + 1) + be - 1,  K a = (tau + 1) L + al;
     P on the inner line tau1, outer line tau3 = tau1 + K/(p(R + 1) - L),
     tau3 = min(tau8, tau9), tau8 = ((S - 1)(L + 1) - K p - 1)/L - 1, tau9 = S - 1 - K/(R + 1).
   Here S is the exact smax (the Lean proof may replace it by a lower bound). */
#ifndef CERTS_H
#define CERTS_H
#include "cert.h"
typedef struct { LL n, d; } Fr;
static LL gcdL(LL a, LL b) { if (a < 0) a = -a; if (b < 0) b = -b; while (b) { LL t = a % b; a = b; b = t; } return a; }
static Fr fr(LL n, LL d) { if (d < 0) { n = -n; d = -d; } LL g = gcdL(n, d); if (g > 1) { n /= g; d /= g; } Fr r = {n, d}; return r; }
static Fr fadd(Fr a, Fr b) { return fr(a.n * b.d + b.n * a.d, a.d * b.d); }
static Fr fsub(Fr a, Fr b) { return fr(a.n * b.d - b.n * a.d, a.d * b.d); }
static Fr fmulq(Fr a, Fr b) { return fr(a.n * b.n, a.d * b.d); }
static Fr fint(LL n) { Fr r = {n, 1}; return r; }
static int fle(Fr a, Fr b) { return a.n * b.d <= b.n * a.d; }
static Fr frmin(Fr a, Fr b) { return fle(a, b) ? a : b; }
/* corners: P = (Pa, Pc), delta; build Cert with common denominator */
static Cert mkFromP(Fr Pa, Fr Pc, Fr dl, ll p1, ll q1, ll p2, ll q2, int fam, int o) {
  Cert c; c.fam = fam; c.o = o; c.p1 = p1; c.q1 = q1; c.p2 = p2; c.q2 = q2;
  LL D = Pa.d / gcdL(Pa.d, Pc.d) * Pc.d;
  D = D / gcdL(D, dl.d) * dl.d;
  c.Dn = D; c.an = Pa.n * (D / Pa.d); c.cn = Pc.n * (D / Pc.d); c.dn = dl.n * (D / dl.d);
  return c;
}
static int lastEdge;
/* w1 = (p, q), w2 = (p2, q2) with p q2 - p2 q = 1 (p2, q2 from egcd, normalised) */
static Cert certEdge(ll N, ll u, ll up, int o, int fam, ll p, ll q, int edge) {
  ll x = o ? up : u, y = o ? u : up;
  ll K, R, al, be, smax, amin;
  Cert bad; bad.Dn = 0;
  if (fam > 0 && y < 3) return bad;
  ll ex, ey;
  if (egcd2(p, q, &ex, &ey) != 1) return bad;
  ll p2 = -ey, q2 = ex; /* p ex + q ey = 1 -> p q2 - p2 q = 1 */
  /* normalise: smallest q2 >= 0 ... keep as is but shift by w1 so that 0 <= q2 < q */
  while (q2 < 0) { q2 += q; p2 += p; }
  while (q2 >= q && q > 0) { q2 -= q; p2 -= p; }
  if (q == 1) { p2 = p - 1; q2 = 1; }
  comboParams(N, y, fam, &K, &R, &al, &be, &smax, &amin);
  LL L = x, S = smax;
  if (edge == 0) edge = (q * L > p * (R + 1)) ? 4 : (p * R > q * (L + 1) ? 1 : 0);
  lastEdge = edge;
  if (edge == 4) {
    if (q * (L + 1) - p * R <= 0) return bad;
    Fr s8 = fsub(fint(S - 1), fr(K * p, L + 1));
    Fr s9 = fsub(fr((S - 1) * (R + 1) - K * q - 1, R), fint(1));
    Fr s1 = frmin(s8, s9);
    Fr s3 = fsub(s1, fr(K, q * (L + 1) - p * R));
    Fr Pa = fr(s1.n * (L + 1) + (al - 1) * s1.d, s1.d * K);
    Fr Pc = fr((s1.n + s1.d) * R + be * s1.d, s1.d * K);
    Fr Qc = fr((s3.n + s3.d) * R + be * s3.d, s3.d * K);
    Fr dl = fmulq(fsub(fsub(Qc, Pc), fint(q2)), fr(1, q));
    return mkFromP(Pa, Pc, dl, p, q, p2, q2, fam, o);
  } else if (edge == 1) {
    if (p * (R + 1) - q * L <= 0) return bad;
    Fr t8 = fsub(fr((S - 1) * (L + 1) - K * p - 1, L), fint(1));
    Fr t9 = fsub(fint(S - 1), fr(K * q, R + 1));
    Fr t3 = frmin(t8, t9);
    Fr t1 = fsub(t3, fr(K, p * (R + 1) - q * L));
    Fr Pa = fr((t1.n + t1.d) * L + al * t1.d, t1.d * K);
    Fr Pc = fr(t1.n * (R + 1) + (be - 1) * t1.d, t1.d * K);
    Fr Qc = fr(t3.n * (R + 1) + (be - 1) * t3.d, t3.d * K);
    Fr dl = fmulq(fsub(fsub(Qc, Pc), fint(q2)), fr(1, q));
    return mkFromP(Pa, Pc, dl, p, q, p2, q2, fam, o);
  }
  return bad;
}
/* which: decimal code o f p q e : orientation, family, w1 = (p, q), edge (0 auto, 1, 4) */
static Cert mkCert(int w, ll N, ll u, ll up) {
  int e = w % 10, q = (w / 10) % 10, p = (w / 100) % 10, f = (w / 1000) % 10, o = (w / 10000) % 10;
  return certEdge(N, u, up, o, f, p, q, e);
}
#endif

/* keys.h: the key conditions of the edge certificates (keys.py / keypoly.py), exact.
   Family params: K, L, R, al, be, s0 = s0n/2 (a lower bound of smax), amin.
   edge4Keys / edge1Keys return 1 iff all key conditions hold. */
#ifndef KEYS_H
#define KEYS_H
#include "certs.h"
typedef struct { LL K, L, R, al, be, s0n, amin; } Fam; /* s0 = s0n / 2 */
static Fam famZo(ll N, ll x, ll y) { Fam f = {N + 2, x, y, 0, 1, N + 1, 2}; return f; }
static Fam famX0o(ll N, ll x, ll y) { Fam f = {N, x, y - 2, 0, 1, N, 1}; return f; }
static Fam famX1o(ll N, ll x, ll y) { Fam f = {N, x, y - 2, 1, 0, N - 1, 2}; return f; }
static int keyFail;
static int edge4Keys(Fam f, ll p, ll q) {
  LL K = f.K, L = f.L, R = f.R;
  LL D = q * (L + 1) - p * R;
  keyFail = 1;
  if (R < 1 || D <= 0 || q * L < p * (R + 1)) return 0;
  Fr s0 = fr(f.s0n, 2);
  keyFail = 2;
  if (!fle(fint(R + 1), s0) || !fle(fint(3), s0)) return 0;
  Fr s8 = fsub(fsub(s0, fint(1)), fr(K * p, L + 1));
  Fr s9 = fsub(fmulq(fsub(fmulq(fsub(s0, fint(1)), fint(R + 1)), fint(K * q + 1)), fr(1, R)), fint(1));
  Fr ss[2] = {s8, s9};
  for (int i = 0; i < 2; i++) {
    Fr s = fsub(ss[i], fr(K, D));
    /* chord: (s(L+1) - 1 + Kp)(R+1) - ((s+1)R + 1 + Kq)L - L(R+1) >= 0 */
    Fr ch = fsub(fsub(fmulq(fadd(fmulq(s, fint(L + 1)), fint(K * p - 1)), fint(R + 1)),
                      fmulq(fadd(fmulq(fadd(s, fint(1)), fint(R)), fint(1 + K * q)), fint(L))), fint(L * (R + 1)));
    keyFail = 10 + 10 * i;
    if (ch.n < 0) return 0;
    keyFail = 11 + 10 * i;
    if (!fle(fint(L + 1), s) || !fle(fint(R + 1), s)) return 0;
    keyFail = 12 + 10 * i;
    if (!fle(fint(f.amin * K - f.al + 1), fmulq(s, fint(L + 1)))) return 0;
  }
  keyFail = 0;
  return 1;
}
static int edge1Keys(Fam f, ll p, ll q) {
  LL K = f.K, L = f.L, R = f.R;
  LL D = p * (R + 1) - q * L;
  keyFail = 1;
  if (R < 1 || D <= 0 || p * R < q * (L + 1)) return 0;
  Fr s0 = fr(f.s0n, 2);
  keyFail = 2;
  if (!fle(fint(R + 1), s0) || !fle(fint(3), s0)) return 0;
  Fr t8 = fsub(fmulq(fsub(fmulq(fsub(s0, fint(1)), fint(L + 1)), fint(K * p + 1)), fr(1, L)), fint(1));
  Fr t9 = fsub(fsub(s0, fint(1)), fr(K * q, R + 1));
  Fr ts[2] = {t8, t9};
  for (int i = 0; i < 2; i++) {
    Fr t = fsub(ts[i], fr(K, D));
    /* chord: (t(R+1) - 1 + Kq)(L+1) - ((t+1)L + 1 + Kp)R - R(L+1) >= 0 */
    Fr ch = fsub(fsub(fmulq(fadd(fmulq(t, fint(R + 1)), fint(K * q - 1)), fint(L + 1)),
                      fmulq(fadd(fmulq(fadd(t, fint(1)), fint(L)), fint(1 + K * p)), fint(R))), fint(R * (L + 1)));
    keyFail = 10 + 10 * i;
    if (ch.n < 0) return 0;
    keyFail = 11 + 10 * i;
    if (!fle(fint(L + 1), t) || !fle(fint(R + 1), t)) return 0;
    keyFail = 12 + 10 * i;
    if (!fle(fint(f.amin * K - f.al), fmulq(fadd(t, fint(1)), fint(L)))) return 0;
  }
  keyFail = 0;
  return 1;
}
/* the bulk certificates: A = Z (u', u) (1,1) f4;  B4 = Z (u', u) (2,1) f4;  B1 = Z (u', u) (2,1) f1 */
static int keyA(ll N, ll u, ll up) { return edge4Keys(famZo(N, up, u), 1, 1); }
static int keyB4(ll N, ll u, ll up) { return edge4Keys(famZo(N, up, u), 2, 1); }
static int keyB1(ll N, ll u, ll up) { return edge1Keys(famZo(N, up, u), 2, 1); }
#endif

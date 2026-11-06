/* pi.h: the "pair" test.  For a combo (K, L = x, R, al, be, smax, amin) and a pair (a, c),
   the witnesses s are the integers in
     lower: (aK - al + 1)/(L + 1), (cK - be + 1)/(R + 1), max(R, 2)
     upper: (aK - al)/L, (cK - be)/R (R >= 1), smax.
   piOK: every upper minus every lower is >= 1 (real numbers), so an integer s exists
   (position-free for this (a, c)).  exactOK: ceil(max lower) <= floor(min upper). */
#ifndef PI_H
#define PI_H
#include "common.h"
static int piOK(ll K, ll L, ll R, ll al, ll be, ll smax, ll amin, ll a, ll c) {
  if (a < amin || c < 1 || L < 1) return 0;
  ll A = a * K - al, C = c * K - be;
  if (A < 0 || C < 0) return 0;
  ll R2 = R > 2 ? R : 2;
  /* uppers: A/L, C/R, smax ; lowers: (A+1)/(L+1), (C+1)/(R+1), R2 */
  /* A/L - (A+1)/(L+1) >= 1 */
  if (A * (L + 1) - (A + 1) * L < L * (L + 1)) return 0;
  if (A * (R + 1) - (C + 1) * L < L * (R + 1)) return 0;
  if (A - R2 * L < L) return 0;
  if (R >= 1) {
    if (C * (L + 1) - (A + 1) * R < R * (L + 1)) return 0;
    if (C * (R + 1) - (C + 1) * R < R * (R + 1)) return 0;
    if (C - R2 * R < R) return 0;
  }
  if (smax * (L + 1) - (A + 1) < L + 1) return 0;
  if (smax * (R + 1) - (C + 1) < R + 1) return 0;
  if (smax - R2 < 1) return 0;
  return 1;
}
static int exactOK(ll K, ll L, ll R, ll al, ll be, ll smax, ll amin, ll a, ll c) {
  if (a < amin || c < 1 || L < 1) return 0;
  ll A = a * K - al, C = c * K - be;
  if (A < 0 || C < 0) return 0;
  ll lo = cdiv(A + 1, L + 1), t = cdiv(C + 1, R + 1);
  if (t > lo) lo = t;
  if (R > lo) lo = R;
  if (2 > lo) lo = 2;
  ll hi = fdiv(A, L);
  if (smax < hi) hi = smax;
  if (R >= 1 && fdiv(C, R) < hi) hi = fdiv(C, R);
  return lo <= hi;
}
#endif

/* common.h: faithful dirOK / dirAll / dirAny (Live8) and the existing regions (ArithCover). */
#ifndef COMMON_H
#define COMMON_H
#include <stdio.h>
#include <stdlib.h>
#include "regs.h"
static ll fdiv(ll a, ll b) { ll q = a / b; if ((a % b != 0) && ((a < 0) != (b < 0))) q--; return q; }
static ll cdiv(ll a, ll b) { return -fdiv(-a, b); }
static int provenOld(ll N, ll u, ll up) {
  return regB(N, u, up) || regB2(N, u, up) || regW(N, u, up) || regD(N, u, up) || regD0(N, u, up);
}
static int isPair(ll N, ll u, ll up) { /* mixed wide non-special, u <= u' */
  if (u < 2 || up < u || u + 2 * up > N - 1) return 0;
  if ((u + N + 1 - up) % 2 != 1 || special(N, u, up)) return 0;
  return 1;
}
/* combos: f = 0: Z (K = M, R = y, al 0, be 1, smax M/2, a >= 2)
           f = 1: X(.,.,0) (K = N, R = y - 2, 0, 1, (N+1)/2, a >= 1)
           f = 2: X(.,.,1) (K = N, R = y - 2, 1, 0, N/2, a >= 2) */
static void comboParams(ll N, ll y, int f, ll *K, ll *R, ll *al, ll *be, ll *smax, ll *amin) {
  if (f == 0) { *K = N + 2; *R = y; *al = 0; *be = 1; *smax = (N + 2) / 2; *amin = 2; }
  else if (f == 1) { *K = N; *R = y - 2; *al = 0; *be = 1; *smax = (N + 1) / 2; *amin = 1; }
  else { *K = N; *R = y - 2; *al = 1; *be = 0; *smax = N / 2; *amin = 2; }
}
#endif

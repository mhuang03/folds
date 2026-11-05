/* Mass of a(2n) = sum_{|X| = n} g(X) h(X) split by the discrepancy of the half-time set X:
   D(y) = |X ∩ [1,y]| - y/2.  Prints, for h = 1/2, 1, 3/2, ..., the mass of {X : max|D| <= h},
   divided by a(n)^2, plus the classes "E-type" (D(2r) = 0 for all r), "D-type" (D(2r+1) = -1/2),
   "D'-type" (D(2r+1) = +1/2).  Usage: discmass N  (N even) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n;
static int ok(unsigned S, int m) {
  int r = m - 1 < n - m ? m - 1 : n - m;
  unsigned L = r ? (((1u << r) - 1) << (m - 1 - r)) : 0;
  unsigned R = r ? (((1u << r) - 1) << m) : 0;
  return __builtin_popcount(S & L) == __builtin_popcount(S & R);
}
int main(int argc, char **argv) {
  n = atoi(argv[1]);
  size_t NS = (size_t)1 << n;
  double *f = calloc(NS, sizeof(double)), *b = calloc(NS, sizeof(double));
  f[0] = 1;
  for (size_t S = 0; S < NS; S++) if (f[S])
    for (int m = 1; m <= n; m++) { unsigned bit = 1u << (m - 1);
      if ((S & bit) || !ok(S, m)) continue; f[S | bit] += f[S]; }
  b[NS - 1] = 1;
  for (size_t S = NS - 1; S-- > 0;) { double v = 0;
    for (int m = 1; m <= n; m++) { unsigned bit = 1u << (m - 1);
      if ((S & bit) || !ok(S, m)) continue; v += b[S | bit]; }
    b[S] = v; }
  /* a(n/2) via the same DP restricted to the first n/2 panels is easier: compute directly */
  int h = n / 2; size_t NH = (size_t)1 << h; double *g = calloc(NH, sizeof(double)); g[0] = 1;
  int save = n; n = h;
  for (size_t S = 0; S < NH; S++) if (g[S])
    for (int m = 1; m <= n; m++) { unsigned bit = 1u << (m - 1);
      if ((S & bit) || !ok(S, m)) continue; g[S | bit] += g[S]; }
  double ah = g[NH - 1]; n = save;
  double mass[40] = {0}, mE = 0, mD = 0, mD2 = 0, tot = 0; long cnt[40] = {0};
  for (size_t S = 0; S < NS; S++) if (__builtin_popcount(S) == h) {
    double v = f[S] * b[S]; tot += v;
    int c = 0, mx = 0, isE = 1, isD = 1, isD2 = 1; /* twice the discrepancy */
    for (int y = 1; y <= n; y++) { c += (S >> (y - 1) & 1) ? 1 : -1; int a = c < 0 ? -c : c; if (a > mx) mx = a;
      if (y % 2 == 0 && c != 0) isE = 0; if (y % 2 == 1 && c != -1) isD = 0; if (y % 2 == 1 && c != 1) isD2 = 0; }
    for (int k = mx; k < 40; k++) { mass[k] += v; if (v > 0) cnt[k]++; }
    if (isE) mE += v; if (isD) mD += v; if (isD2) mD2 += v;
  }
  double a2 = ah * ah;
  printf("N=%d a(N)=%.0f a(n)=%.0f  a(N)/a(n)^2=%.4f\n", n, tot, ah, tot / a2);
  printf("  E-type %.4f  D-type %.4f  D'-type %.4f   (per a(n)^2)\n", mE / a2, mD / a2, mD2 / a2);
  for (int k = 1; k <= n / 2 && k < 40; k++) printf("  max|D| <= %d/2: %.4f  (%ld sets)\n", k, mass[k] / a2, cnt[k]);
  return 0;
}

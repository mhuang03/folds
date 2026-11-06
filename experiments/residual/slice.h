/* slice.h: the slice test (Lean `sliceCons`, `RegionSL`).  Fix a = p c + j; the witness
   conditions become eight integer linear forms in (s, c):
     g1 = -L s + pK c + (jK - al)          (aK >= sL + al)
     g2 = (L+1) s - pK c + (al - 1 - jK)   (aK + 1 <= s(L+1) + al)
     g3 = -R s + K c - be                  (cK >= sR + be)
     g4 = (R+1) s - K c + (be - 1)         (cK + 1 <= sR + be + s)
     g5 = s - 2, g6 = s - R, g7 = smax - s, g8 = p c + j - amin.
   A lattice point (s, c) with all g >= 0 is a witness.  ParOK (parok.h) with variables (s, c). */
#ifndef SLICE_H
#define SLICE_H
#include "parok.h"
static void buildSlice(ll K, ll L, ll R, ll al, ll be, ll smax, ll amin, ll p, ll j) {
  ng = 0;
#define ADDG(a_, c_, d_) do { gs[ng].A = (a_); gs[ng].C = (c_); gs[ng].D = (d_); ng++; } while (0)
  ADDG(-L, (LL)p * K, (LL)j * K - al);
  ADDG(L + 1, -(LL)p * K, al - 1 - (LL)j * K);
  ADDG(-R, K, -be);
  ADDG(R + 1, -K, be - 1);
  ADDG(1, 0, -2);
  ADDG(1, 0, -R);
  ADDG(-1, 0, smax);
  ADDG(0, p, j - amin);
#undef ADDG
}
/* the swapped slice c = p a + j, in the variables (s, a) (Lean `sliceCons'`) */
static void buildSliceB(ll K, ll L, ll R, ll al, ll be, ll smax, ll amin, ll p, ll j) {
  ng = 0;
#define ADDG(a_, c_, d_) do { gs[ng].A = (a_); gs[ng].C = (c_); gs[ng].D = (d_); ng++; } while (0)
  ADDG(-L, K, -al);
  ADDG(L + 1, -K, al - 1);
  ADDG(-R, (LL)p * K, (LL)j * K - be);
  ADDG(R + 1, -(LL)p * K, be - 1 - (LL)j * K);
  ADDG(1, 0, -2);
  ADDG(1, 0, -R);
  ADDG(-1, 0, smax);
  ADDG(0, 1, -amin);
#undef ADDG
}
static int SLQ = 4, SLS = 16, SLB = 1;
static int sliceAnyDir(void) {
  for (ll k = 0; k <= SLQ; k++)
    for (ll sg = (k == 0 ? 1 : 0); sg <= (k == 0 ? 1 : SLS); sg++)
      if (parOKdir(sg, k)) return 1;
  return 0;
}
/* RegionSL: some family, orientation, slice (a = p c + j or c = p a + j, p <= 3) and direction.
   Only the slices through at least one witness are tried (a slice containing a fundamental
   parallelogram contains a lattice point, i.e. a witness). */
#define MAXW 20000
static ll wa[MAXW], wc[MAXW];
static int seenj(ll *js, int n, ll j) { for (int i = 0; i < n; i++) if (js[i] == j) return 1; return 0; }
static int regionSL(ll N, ll u, ll up) {
  static ll js[MAXW];
  for (int o = 0; o < 2; o++) {
    ll x = o ? up : u, y = o ? u : up;
    for (int f = 0; f < 3; f++) {
      if (f > 0 && y < 3) continue;
      ll K, R, al, be, smax, amin;
      comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
      int nw = 0;
      for (ll s = (R > 2 ? R : 2); s <= smax && nw < MAXW; s++) {
        ll a = cdiv(s * x + al, K);
        if (a * K > s * x + al + s - 1 || a < amin) continue;
        ll c = cdiv(s * R + be, K);
        if (c * K > s * R + be + s - 1) continue;
        wa[nw] = a; wc[nw] = c; nw++;
      }
      for (ll p = 0; p <= 3; p++)
        for (int t = 0; t < 2; t++) {
          if (t == 1 && !SLB) continue;
          int nj = 0;
          for (int i = 0; i < nw; i++) {
            ll j = t == 0 ? wa[i] - p * wc[i] : wc[i] - p * wa[i];
            if (seenj(js, nj, j)) continue;
            js[nj++] = j;
            if (t == 0) buildSlice(K, x, R, al, be, smax, amin, p, j);
            else buildSliceB(K, x, R, al, be, smax, amin, p, j);
            if (sliceAnyDir()) return 1;
          }
        }
    }
  }
  return 0;
}
#endif

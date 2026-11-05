// solver.c: exact background-picture solver, used from Python through ctypes (lib.py).
// solve(N, bg, tg, out): bg, tg are 0/1 arrays indexed 1..N (background panels, target panels);
// panels in neither are absent.  Finds an ordering of the target panels such that every step m
// is balanced (|placed n L(m)| = |placed n R(m)|), placed = background + earlier steps.
// Returns 1 and writes the order to out (preferring, at every step, the smallest key[m]),
// or 0 if none exists.  Target size <= 30.
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

int solve(int N, const int *bg, const int *tg, const int *key, int *out) {
  int T[64], t = 0, dimb[64];
  uint64_t Lm[64], Rm[64];
  for (int x = 1; x <= N; x++) if (tg[x]) T[t++] = x;
  if (t > 30) return -1;
  for (int i = 0; i < t; i++) {
    int m = T[i], r = (m - 1 < N - m) ? m - 1 : N - m, d = 0;
    Lm[i] = Rm[i] = 0;
    for (int j = 0; j < t; j++) {
      int x = T[j];
      if (x >= m - r && x < m) Lm[i] |= 1ull << j;
      if (x > m && x <= m + r) Rm[i] |= 1ull << j;
    }
    for (int x = 1; x <= N; x++) if (bg[x]) {
      if (x >= m - r && x < m) d++; else if (x > m && x <= m + r) d--;
    }
    dimb[i] = d;
  }
  uint64_t full = (1ull << t) - 1;
  uint8_t *good = malloc(full + 1);
  for (int64_t S = full; S >= 0; S--) {
    if ((uint64_t)S == full) { good[S] = 1; continue; }
    int g = 0;
    for (int i = 0; i < t && !g; i++) if (!(S >> i & 1)) {
      int I = dimb[i] + __builtin_popcountll(S & Lm[i]) - __builtin_popcountll(S & Rm[i]);
      if (I == 0 && good[S | (1ull << i)]) g = 1;
    }
    good[S] = g;
  }
  if (!good[0]) { free(good); return 0; }
  uint64_t S = 0;
  int k = 0;
  while (S != full) {
    int best = -1, bk = 1 << 30;
    for (int i = 0; i < t; i++) if (!(S >> i & 1)) {
      int I = dimb[i] + __builtin_popcountll(S & Lm[i]) - __builtin_popcountll(S & Rm[i]);
      if (I == 0 && good[S | (1ull << i)] && key[T[i]] < bk) { bk = key[T[i]]; best = i; }
    }
    out[k++] = T[best];
    S |= 1ull << best;
  }
  free(good);
  return 1;
}

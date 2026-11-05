/* fullcert.c q: rotation-stable sequences in the sig convention of Folds/Live4.lean (`GoodL`):
   pi valid in the q-strip and sig o pi valid, sig(t) = ((nu - t) mod q) + 1.  For every nu in
   [0, q) and every start t, prints "nu t x_1 ... x_q" for one such pi starting with t, or
   "nu t -" if none.  Subset DP (2^q bytes), 1 core; q <= 27. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
  int q = atoi(argv[1]);
  uint32_t L[40], R[40];
  for (int m = 1; m <= q; m++) {
    int r = m - 1 < q - m ? m - 1 : q - m;
    L[m] = R[m] = 0;
    for (int d = 1; d <= r; d++) { L[m] |= 1u << (m - d - 1); R[m] |= 1u << (m + d - 1); }
  }
  uint32_t full = (1u << q) - 1;
  uint8_t *done = malloc((size_t)full + 1);
  for (int nu = 0; nu < q; nu++) {
    int sg[40];
    for (int t = 1; t <= q; t++) sg[t] = ((nu - t) % q + q) % q + 1;
    for (int64_t S = full; S >= 0; S--) {
      if ((uint32_t)S == full) { done[S] = 1; continue; }
      uint32_t Ss = 0;
      for (int t = 1; t <= q; t++) if (S >> (t - 1) & 1) Ss |= 1u << (sg[t] - 1);
      uint8_t ok = 0;
      for (int t = 1; t <= q && !ok; t++) {
        if (S >> (t - 1) & 1) continue;
        if (__builtin_popcount((uint32_t)S & L[t]) != __builtin_popcount((uint32_t)S & R[t])) continue;
        int u = sg[t];
        if (__builtin_popcount(Ss & L[u]) != __builtin_popcount(Ss & R[u])) continue;
        if (done[S | (1u << (t - 1))]) ok = 1;
      }
      done[S] = ok;
    }
    for (int t0 = 1; t0 <= q; t0++) {
      printf("%d %d", nu, t0);
      if (!done[1u << (t0 - 1)]) { printf(" -\n"); continue; }
      uint32_t S = 1u << (t0 - 1);
      printf(" %d", t0);
      while (S != full) {
        uint32_t Ss = 0;
        for (int t = 1; t <= q; t++) if (S >> (t - 1) & 1) Ss |= 1u << (sg[t] - 1);
        int nxt = 0;
        for (int t = 1; t <= q && !nxt; t++) {
          if (S >> (t - 1) & 1) continue;
          if (__builtin_popcount(S & L[t]) != __builtin_popcount(S & R[t])) continue;
          int u = sg[t];
          if (__builtin_popcount(Ss & L[u]) != __builtin_popcount(Ss & R[u])) continue;
          if (done[S | (1u << (t - 1))]) nxt = t;
        }
        printf(" %d", nxt);
        S |= 1u << (nxt - 1);
      }
      printf("\n");
    }
    fflush(stdout);
  }
  free(done);
  return 0;
}

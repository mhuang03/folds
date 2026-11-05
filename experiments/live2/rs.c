/* rs.c k1 k2: rotation-stable sequences (PROOFS.txt 2.3).  For the k-strip and each nu in
   [0, k): which t can start a sequence tau such that tau and its cyclic rotation
   t -> ((t - 1 + nu) mod k) + 1 are both semi-symmetric?  Subset DP: done[S] = the set S
   (bit t-1) can be completed.  Prints the impossible (nu, t). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
  int k1 = atoi(argv[1]), k2 = atoi(argv[2]);
  for (int k = k1; k <= k2; k++) {
    uint32_t L[40], R[40];
    for (int m = 1; m <= k; m++) {
      int r = m - 1 < k - m ? m - 1 : k - m;
      L[m] = R[m] = 0;
      for (int d = 1; d <= r; d++) { L[m] |= 1u << (m - d - 1); R[m] |= 1u << (m + d - 1); }
    }
    uint32_t full = (k == 32) ? 0xffffffffu : ((1u << k) - 1);
    uint8_t *done = malloc((size_t)full + 1);
    printf("%d:", k);
    for (int nu = 0; nu < k; nu++) {
      int rot[40];
      for (int t = 1; t <= k; t++) rot[t] = (t - 1 + nu) % k + 1;
      for (int64_t S = full; S >= 0; S--) {
        if ((uint32_t)S == full) { done[S] = 1; continue; }
        uint32_t Sr = 0;
        for (int t = 1; t <= k; t++) if (S >> (t - 1) & 1) Sr |= 1u << (rot[t] - 1);
        uint8_t ok = 0;
        for (int t = 1; t <= k && !ok; t++) {
          if (S >> (t - 1) & 1) continue;
          if (__builtin_popcount((uint32_t)S & L[t]) != __builtin_popcount((uint32_t)S & R[t])) continue;
          int u = rot[t];
          if (__builtin_popcount(Sr & L[u]) != __builtin_popcount(Sr & R[u])) continue;
          if (done[S | (1u << (t - 1))]) ok = 1;
        }
        done[S] = ok;
      }
      for (int t = 1; t <= k; t++)
        if (!done[1u << (t - 1)]) printf(" (nu=%d,t=%d)", nu, t);
    }
    printf("\n");
    fflush(stdout);
    free(done);
  }
  return 0;
}

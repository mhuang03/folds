/* symadj.c NMAX: for each N <= NMAX and 1 <= r < N, is there a SYMMETRIC ordering of
   [N] \ {r, r+1} (every step: m-d placed <=> m+d placed, d <= reach)?  Subset DP over the
   target set.  Also counts the semi-symmetric case for comparison (mode 1). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv) {
  int NMAX = atoi(argv[1]);
  int mode = argc > 2 ? atoi(argv[2]) : 0; /* 0 symmetric, 1 semi */
  for (int N = 2; N <= NMAX; N++) {
    uint32_t L[64], R[64];
    uint32_t Lp[64][64], Rp[64][64];
    for (int m = 1; m <= N; m++) {
      int r = m - 1 < N - m ? m - 1 : N - m;
      L[m] = R[m] = 0;
      for (int d = 1; d <= r; d++) { L[m] |= 1u << (m - d - 1); R[m] |= 1u << (m + d - 1); }
    }
    uint32_t full = (N == 32) ? 0xffffffffu : ((1u << N) - 1);
    uint8_t *reach = malloc(((size_t)1 << N));
    printf("N=%d:", N);
    for (int rr = 1; rr < N; rr++) {
      uint32_t T = full & ~(3u << (rr - 1));
      memset(reach, 0, (size_t)1 << N);
      reach[0] = 1;
      /* iterate over subsets of T in increasing order */
      uint32_t S = 0;
      for (;;) {
        if (reach[S]) {
          for (int m = 1; m <= N; m++) {
            if (!(T >> (m - 1) & 1) || (S >> (m - 1) & 1)) continue;
            int ok;
            if (mode == 0) {
              /* reflect left arm onto right arm: bit m-d -> m+d */
              uint32_t l = S & L[m], rgt = S & R[m];
              uint32_t refl = 0;
              for (uint32_t t = l; t; t &= t - 1) {
                int b = __builtin_ctz(t); /* panel b+1 = m-d */
                int d = m - (b + 1);
                refl |= 1u << (m + d - 1);
              }
              ok = refl == rgt;
            } else
              ok = __builtin_popcount(S & L[m]) == __builtin_popcount(S & R[m]);
            if (ok) reach[S | (1u << (m - 1))] = 1;
          }
        }
        if (S == T) break;
        S = (S - T) & T;
      }
      printf(" %d", reach[T] ? 1 : 0);
    }
    printf("\n");
    free(reach);
    fflush(stdout);
  }
  return 0;
}

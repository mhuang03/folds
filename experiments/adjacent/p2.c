/* p2.c NMIN NMAX: P2(N, r) = order [r+2, N] validly in the N-strip on the background {r, r+1}
   (both present, never checked).  Prints, per N, the r for which it fails, and with -v the
   lexicographically first solution (greedy from the bottom). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int N;
static uint32_t L[40], R[40];
static int valid(uint32_t S, int m) {
  return __builtin_popcount(S & L[m]) == __builtin_popcount(S & R[m]);
}
int main(int argc, char **argv) {
  int NMIN = atoi(argv[1]), NMAX = atoi(argv[2]);
  int verbose = argc > 3;
  uint8_t *B = malloc((size_t)1 << NMAX);
  for (N = NMIN; N <= NMAX; N++) {
    for (int m = 1; m <= N; m++) {
      int r = m - 1 < N - m ? m - 1 : N - m;
      L[m] = R[m] = 0;
      for (int d = 1; d <= r; d++) { L[m] |= 1u << (m - d - 1); R[m] |= 1u << (m + d - 1); }
    }
    printf("N=%d fail:", N);
    for (int r = 1; r + 1 <= N; r++) {
      uint32_t bg = 3u << (r - 1);
      uint32_t T = ((N == 32 ? 0xffffffffu : (1u << N) - 1)) & ~((1u << (r + 1)) - 1);
      /* index subsets of T by shifting: T = bits r+1 .. N-1 */
      int sh = r + 1, k = N - r - 1;
      uint32_t full = (1u << k) - 1;
      memset(B, 0, (size_t)1 << k);
      B[full] = 1;
      for (uint32_t s = full; ; s--) {
        if (s != full)
          for (int i = 0; i < k; i++)
            if (!(s >> i & 1) && B[s | 1u << i] && valid((s << sh) | bg, i + sh + 1)) { B[s] = 1; break; }
        if (s == 0) break;
      }
      if (!B[0]) printf(" %d", r);
      else if (verbose) {
        printf("\n  r=%d:", r);
        uint32_t u = 0;
        while (u != full)
          for (int ii = 0; ii < k; ii++) {
            int i = argv[3][0] == 't' ? k - 1 - ii : ii; /* 't': greedy from the top */
            if (!(u >> i & 1) && valid((u << sh) | bg, i + sh + 1) && B[u | 1u << i]) {
              printf(" %d", i + sh + 1); u |= 1u << i; break;
            }
          }
      }
      (void)T;
    }
    printf("\n");
    fflush(stdout);
  }
  return 0;
}

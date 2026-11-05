/* qj.c NMAX: QJ(n, t) in the half-infinite strip (window of y = [1, 2y-1]): order [t+1, n]
   with the panels > n present (background) and [1, t] absent.  Prints failures; with a 2nd
   argument also solutions (greedy from the top). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int n, t;
/* bit i = panel t+1+i, i < n-t */
static int valid(uint32_t S, int y) {
  int i = y - t - 1;
  int l = __builtin_popcount(S & ((1u << i) - 1));
  int hi = 2 * y - 1;
  int hk = hi < n ? hi : n;
  int j = hk - t;
  int r = __builtin_popcount(S & ((1u << j) - 1) & ~((1u << (i + 1)) - 1));
  if (hi > n) r += hi - n;
  return l == r;
}
int main(int argc, char **argv) {
  int NMAX = atoi(argv[1]);
  int verbose = argc > 2;
  for (n = 1; n <= NMAX; n++) {
    printf("n=%d fail t:", n);
    for (t = 0; t < n; t++) {
      int w = n - t;
      uint32_t full = (1u << w) - 1;
      uint8_t *B = calloc((size_t)1 << w, 1);
      B[full] = 1;
      for (uint32_t S = full;; S--) {
        if (S != full)
          for (int i = 0; i < w; i++)
            if (!(S >> i & 1) && B[S | 1u << i] && valid(S, t + 1 + i)) { B[S] = 1; break; }
        if (S == 0) break;
      }
      if (!B[0]) printf(" %d", t);
      else if (verbose) {
        printf("\n   t=%d:", t);
        uint32_t U = 0;
        while (U != full)
          for (int i = w - 1; i >= 0; i--)
            if (!(U >> i & 1) && valid(U, t + 1 + i) && B[U | 1u << i]) {
              printf(" %d", t + 1 + i); U |= 1u << i; break;
            }
      }
      free(B);
    }
    printf("\n");
    fflush(stdout);
  }
  return 0;
}

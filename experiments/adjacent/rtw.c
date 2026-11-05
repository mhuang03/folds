/* rtw.c MAX: R(t, w) in the half-infinite strip (window of y = [1, 2y-1]): order [t+1, t+w]
   on the background [1, t] (present), nothing beyond t + w.  Prints failures and, with a 2nd
   argument, the solution greedy from the top. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int t, w;
/* S = placed subset of [t+1, t+w], bit i = panel t+1+i */
static int valid(uint32_t S, int y) {
  /* left [1, y-1]: background t (y > t always) + placed in [t+1, y-1] */
  int i = y - t - 1;
  int l = t + __builtin_popcount(S & ((1u << i) - 1));
  int hi = 2 * y - 1;
  if (hi > t + w) hi = t + w;
  int j = hi - t; /* panels t+1..hi -> bits 0..j-1 */
  int r = __builtin_popcount(S & ((1u << j) - 1) & ~((1u << (i + 1)) - 1));
  return l == r;
}
int main(int argc, char **argv) {
  int MAX = atoi(argv[1]);
  int verbose = argc > 2;
  for (int s = 2; s <= MAX; s++)
    for (t = 1; t < s; t++) {
      w = s - t;
      uint32_t full = (1u << w) - 1;
      uint8_t *B = calloc((size_t)1 << w, 1);
      B[full] = 1;
      for (uint32_t S = full;; S--) {
        if (S != full)
          for (int i = 0; i < w; i++)
            if (!(S >> i & 1) && B[S | 1u << i] && valid(S, t + 1 + i)) { B[S] = 1; break; }
        if (S == 0) break;
      }
      if (!B[0]) printf("R(%d,%d) FAILS\n", t, w);
      else if (verbose) {
        printf("R(%d,%d):", t, w);
        uint32_t U = 0;
        while (U != full)
          for (int i = w - 1; i >= 0; i--)
            if (!(U >> i & 1) && valid(U, t + 1 + i) && B[U | 1u << i]) {
              printf(" %d", t + 1 + i); U |= 1u << i; break;
            }
        printf("\n");
      }
      free(B);
    }
  return 0;
}

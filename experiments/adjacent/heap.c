/* heap.c NMAX d: is there a valid (semi-symmetric) full sequence of the n-strip in which
   every x precedes 2x, 2x+1, ..., 2x+d-1 (those <= n)?  ("d-heap order")
   Shift lemma: then [d+1, n+d] is reachable in the (n+d)-strip.  Prints per n. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
int main(int argc, char **argv) {
  int NMAX = atoi(argv[1]), d = atoi(argv[2]);
  int show = argc > 3;
  for (int n = 1; n <= NMAX; n++) {
    uint32_t L[40], R[40], par[40];
    for (int m = 1; m <= n; m++) {
      int r = m - 1 < n - m ? m - 1 : n - m;
      L[m] = R[m] = 0;
      for (int k = 1; k <= r; k++) { L[m] |= 1u << (m - k - 1); R[m] |= 1u << (m + k - 1); }
      par[m] = 0;
      for (int x = 1; x < m; x++) if (2 * x <= m && m <= 2 * x + d - 1) par[m] |= 1u << (x - 1);
    }
    uint32_t full = (1u << n) - 1;
    uint8_t *B = calloc((size_t)1 << n, 1);
    B[full] = 1;
    for (uint32_t S = full;; S--) {
      if (S != full)
        for (int m = 1; m <= n; m++)
          if (!(S >> (m - 1) & 1) && (par[m] & ~S) == 0 &&
              __builtin_popcount(S & L[m]) == __builtin_popcount(S & R[m]) && B[S | 1u << (m - 1)]) {
            B[S] = 1; break;
          }
      if (S == 0) break;
    }
    printf("n=%d d=%d: %s", n, d, B[0] ? "YES" : "no");
    if (B[0] && show) {
      uint32_t U = 0;
      printf(" :");
      while (U != full)
        for (int m = n; m >= 1; m--)
          if (!(U >> (m - 1) & 1) && (par[m] & ~U) == 0 &&
              __builtin_popcount(U & L[m]) == __builtin_popcount(U & R[m]) && B[U | 1u << (m - 1)]) {
            printf(" %d", m); U |= 1u << (m - 1); break;
          }
    }
    printf("\n");
    fflush(stdout);
    free(B);
  }
  return 0;
}

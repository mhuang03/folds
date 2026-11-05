/* jseg.c N: for every k, order the initial segment [1, k] validly in the N-strip
   (J(N, k)); prints the lexicographically first solution with the LARGEST first panel
   (greedy from the top). */
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
  N = atoi(argv[1]);
  for (int m = 1; m <= N; m++) {
    int r = m - 1 < N - m ? m - 1 : N - m;
    L[m] = R[m] = 0;
    for (int d = 1; d <= r; d++) { L[m] |= 1u << (m - d - 1); R[m] |= 1u << (m + d - 1); }
  }
  for (int k = 1; k <= N; k++) {
    uint32_t T = (1u << k) - 1;
    uint8_t *B = calloc((size_t)1 << k, 1);
    B[T] = 1;
    uint32_t S = T;
    for (;;) {
      if (S != T)
        for (int y = 1; y <= k; y++)
          if (!(S >> (y - 1) & 1) && B[S | 1u << (y - 1)] && valid(S, y)) { B[S] = 1; break; }
      if (S == 0) break;
      S--;
    }
    printf("J(%d,%d): %s", N, k, B[0] ? "YES" : "no");
    if (B[0]) {
      printf("  greedy-top:");
      uint32_t U = 0;
      while (U != T)
        for (int y = k; y >= 1; y--)
          if (!(U >> (y - 1) & 1) && valid(U, y) && B[U | 1u << (y - 1)]) {
            printf(" %d", y); U |= 1u << (y - 1); break;
          }
    }
    printf("\n");
    free(B);
  }
  return 0;
}

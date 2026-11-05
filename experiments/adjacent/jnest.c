/* jnest.c K N0 N1: is there one ordering of [1, K] that is valid in the N-strip for every
   N0 <= N <= N1 simultaneously?  Prints the lexicographically first (greedy from the top). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static uint32_t L[64][40], R[64][40];
static int K, N0, N1;
static int only2 = 0; /* env ONLY2: check only N0 and N1 */
static int ok(uint32_t S, int m) {
  for (int N = N0; N <= N1; N = (only2 && N < N1) ? N1 : N + 1)
    if (__builtin_popcount(S & L[N][m]) != __builtin_popcount(S & R[N][m])) return 0;
  return 1;
}
int main(int argc, char **argv) {
  K = atoi(argv[1]); N0 = atoi(argv[2]); N1 = atoi(argv[3]);
  only2 = getenv("ONLY2") != NULL;
  for (int N = N0; N <= N1; N++)
    for (int m = 1; m <= K; m++) {
      int rr = m - 1 < N - m ? m - 1 : N - m;
      L[N][m] = R[N][m] = 0;
      for (int d = 1; d <= rr; d++) {
        L[N][m] |= 1u << (m - d - 1);
        if (m + d <= K) R[N][m] |= 1u << (m + d - 1);
      }
    }
  uint32_t T = (1u << K) - 1;
  uint8_t *B = calloc((size_t)1 << K, 1);
  B[T] = 1;
  for (uint32_t S = T;; S--) {
    if (S != T)
      for (int m = 1; m <= K; m++)
        if (!(S >> (m - 1) & 1) && B[S | 1u << (m - 1)] && ok(S, m)) { B[S] = 1; break; }
    if (S == 0) break;
  }
  printf("K=%d N=%d..%d: %s", K, N0, N1, B[0] ? "YES" : "no");
  if (B[0]) {
    uint32_t U = 0;
    printf(" :");
    while (U != T)
      for (int m = K; m >= 1; m--)
        if (!(U >> (m - 1) & 1) && ok(U, m) && B[U | 1u << (m - 1)]) { printf(" %d", m); U |= 1u << (m - 1); break; }
  }
  printf("\n");
  return 0;
}

/* nested.c N0 N1 [r]: is there an ordering of [N1] \ D (D = {r, r+1}, or empty if r = 0)
   whose restriction to [N] is a valid (semi-symmetric) ordering of [N] \ D for EVERY
   N0 <= N <= N1?  Subset DP.  Prints the lexicographically first such ordering. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static uint32_t L[40][40], R[40][40]; /* [N][m] */
static int N0, N1;
static int ok(uint32_t S, int m) {
  int lo = m > N0 ? m : N0;
  for (int N = lo; N <= N1; N++)
    if (__builtin_popcount(S & L[N][m]) != __builtin_popcount(S & R[N][m])) return 0;
  return 1;
}
int main(int argc, char **argv) {
  N0 = atoi(argv[1]); N1 = atoi(argv[2]);
  int r = argc > 3 ? atoi(argv[3]) : 0;
  for (int N = 1; N <= N1; N++)
    for (int m = 1; m <= N; m++) {
      int rr = m - 1 < N - m ? m - 1 : N - m;
      L[N][m] = R[N][m] = 0;
      for (int d = 1; d <= rr; d++) { L[N][m] |= 1u << (m - d - 1); R[N][m] |= 1u << (m + d - 1); }
    }
  uint32_t full = (1u << N1) - 1;
  uint32_t T = r ? full & ~(3u << (r - 1)) : full;
  uint8_t *B = calloc((size_t)1 << N1, 1);
  /* backward DP: B[S] = T completable from S */
  B[T] = 1;
  uint32_t S = T;
  for (;;) {
    if (S != T)
      for (int m = 1; m <= N1; m++)
        if ((T >> (m - 1) & 1) && !(S >> (m - 1) & 1) && B[S | 1u << (m - 1)] && ok(S, m)) {
          B[S] = 1;
          break;
        }
    if (S == 0) break;
    S = (S - 1) & T;
  }
  printf("N0=%d N1=%d r=%d: %s", N0, N1, r, B[0] ? "YES" : "no");
  if (B[0]) {
    printf("  lexfirst:");
    uint32_t U = 0;
    while (U != T)
      for (int m = 1; m <= N1; m++)
        if ((T >> (m - 1) & 1) && !(U >> (m - 1) & 1) && ok(U, m) && B[U | 1u << (m - 1)]) {
          printf(" %d", m); U |= 1u << (m - 1); break;
        }
  }
  printf("\n");
  return 0;
}

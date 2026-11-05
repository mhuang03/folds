/* adjinfo.c N [r]: for the target T = [N] \ {r, r+1}: forward DP F (subsets of T reachable from
   scratch) and backward DP B (subsets from which T can be completed).  Prints the panels that
   can come first / last, and the number of valid orderings (mod 2^64) when N <= 20.
   Generic: target given as complement of a list of panels with option -d a,b,c. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int N;
static uint32_t L[64], R[64];
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
  uint32_t full = (1u << N) - 1;
  int r0 = 1, r1 = N - 1;
  if (argc > 2) r0 = r1 = atoi(argv[2]);
  uint8_t *F = malloc((size_t)1 << N), *B = malloc((size_t)1 << N);
  for (int rr = r0; rr <= r1; rr++) {
    uint32_t T = full & ~(3u << (rr - 1));
    memset(F, 0, (size_t)1 << N);
    memset(B, 0, (size_t)1 << N);
    F[0] = 1;
    uint32_t S = 0;
    for (;;) {
      if (F[S])
        for (int m = 1; m <= N; m++)
          if ((T >> (m - 1) & 1) && !(S >> (m - 1) & 1) && valid(S, m)) F[S | 1u << (m - 1)] = 1;
      if (S == T) break;
      S = (S - T) & T;
    }
    if (!F[T]) { printf("N=%d r=%d: NOT co-reachable\n", N, rr); continue; }
    /* backward: B[S] = 1 if T completable from S; iterate subsets of T decreasing */
    B[T] = 1;
    S = T;
    for (;;) {
      /* S runs over subsets in decreasing order */
      if (S != T) {
        for (int m = 1; m <= N; m++)
          if ((T >> (m - 1) & 1) && !(S >> (m - 1) & 1) && valid(S, m) && B[S | 1u << (m - 1)]) {
            B[S] = 1;
            break;
          }
      }
      if (S == 0) break;
      S = (S - 1) & T;
    }
    printf("N=%d r=%d first:", N, rr);
    for (int m = 1; m <= N; m++)
      if ((T >> (m - 1) & 1) && B[1u << (m - 1)]) printf(" %d", m);
    printf("  last:");
    for (int m = 1; m <= N; m++)
      if ((T >> (m - 1) & 1) && F[T & ~(1u << (m - 1))] && valid(T & ~(1u << (m - 1)), m))
        printf(" %d", m);
    printf("\n  lexfirst:");
    {
      uint32_t U = 0;
      while (U != T) {
        for (int m = 1; m <= N; m++)
          if ((T >> (m - 1) & 1) && !(U >> (m - 1) & 1) && valid(U, m) && B[U | 1u << (m - 1)]) {
            printf(" %d", m); U |= 1u << (m - 1); break;
          }
      }
      printf("\n  lexlast(max first):");
      U = 0;
      while (U != T) {
        for (int m = N; m >= 1; m--)
          if ((T >> (m - 1) & 1) && !(U >> (m - 1) & 1) && valid(U, m) && B[U | 1u << (m - 1)]) {
            printf(" %d", m); U |= 1u << (m - 1); break;
          }
      }
    }
    printf("\n");
  }
  return 0;
}

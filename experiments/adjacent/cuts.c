/* cuts.c N mode a [b]: intermediate sets X on some valid ordering of the target T (forward
   reachable from scratch inside T, and T completable from X) that are unions of at most two
   intervals.  mode j: T = [1, a] (initial segment).  mode d: T = [N] \ {a, a+1}.
   mode p: T = [a+2, N] on the background {a, a+1} (P2). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int N;
static uint32_t L[40], R[40];
static int valid(uint32_t S, int m) {
  return __builtin_popcount(S & L[m]) == __builtin_popcount(S & R[m]);
}
static int runs(uint32_t X) { /* number of maximal intervals */
  int c = 0;
  for (int i = 0; i < N; i++)
    if ((X >> i & 1) && !(i > 0 && (X >> (i - 1) & 1))) c++;
  return c;
}
int main(int argc, char **argv) {
  N = atoi(argv[1]);
  char mode = argv[2][0];
  int a = atoi(argv[3]);
  for (int m = 1; m <= N; m++) {
    int r = m - 1 < N - m ? m - 1 : N - m;
    L[m] = R[m] = 0;
    for (int d = 1; d <= r; d++) { L[m] |= 1u << (m - d - 1); R[m] |= 1u << (m + d - 1); }
  }
  uint32_t full = (1u << N) - 1, T, bg = 0;
  if (mode == 'j') T = (1u << a) - 1;
  else if (mode == 'd') T = full & ~(3u << (a - 1));
  else { T = full & ~((1u << (a + 1)) - 1); bg = 3u << (a - 1); }
  uint8_t *F = calloc((size_t)1 << N, 1), *B = calloc((size_t)1 << N, 1);
  F[0] = 1;
  for (uint32_t S = 0;; S = (S - T) & T) {
    if (F[S])
      for (int m = 1; m <= N; m++)
        if ((T >> (m - 1) & 1) && !(S >> (m - 1) & 1) && valid(S | bg, m)) F[S | 1u << (m - 1)] = 1;
    if (S == T) break;
  }
  B[T] = 1;
  for (uint32_t S = T;; S = (S - 1) & T) {
    if (S != T)
      for (int m = 1; m <= N; m++)
        if ((T >> (m - 1) & 1) && !(S >> (m - 1) & 1) && valid(S | bg, m) && B[S | 1u << (m - 1)]) { B[S] = 1; break; }
    if (S == 0) break;
  }
  printf("N=%d mode=%c a=%d solvable=%d\n", N, mode, a, B[0]);
  for (uint32_t S = T;; S = (S - 1) & T) {
    int c = __builtin_popcount(S);
    if (F[S] && B[S] && c >= 2 && c <= __builtin_popcount(T) - 2 && runs(S) <= 2) {
      printf("  ");
      for (int i = 0; i < N; i++)
        if (S >> i & 1) {
          int j = i;
          while (j + 1 < N && (S >> (j + 1) & 1)) j++;
          printf("[%d,%d] ", i + 1, j + 1);
          i = j;
        }
      printf("\n");
    }
    if (S == 0) break;
  }
  return 0;
}

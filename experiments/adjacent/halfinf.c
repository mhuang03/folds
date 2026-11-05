/* halfinf.c KMAX: problems in the half-infinite strip (windows [1, 2y-1], i.e. panels of the
   left half of a large strip).
   I(k):  order [1, k] from scratch.
   Q(n):  order [1, n-2] with the panels >= n+1 all present (background), n-1, n absent.
   Prints solvability and the lexicographically first solution. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int K;              /* number of panels to order: [1, K] */
static int bgfrom;         /* background: panels >= bgfrom present (0 = none) */
static int valid(uint32_t S, int y) {
  int l = __builtin_popcount(S & ((1u << (y - 1)) - 1));
  int hi = 2 * y - 1; /* right arm [y+1, 2y-1] */
  int hk = hi < K ? hi : K;
  int r = 0;
  if (hk > y) r = __builtin_popcount(S & (((1u << hk) - 1) & ~((1u << y) - 1)));
  if (bgfrom && hi >= bgfrom) r += hi - bgfrom + 1;
  return l == r;
}
static void solve(const char *name, int k) {
  uint32_t T = (k == 32) ? 0xffffffffu : ((1u << k) - 1);
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
  printf("%s: %s", name, B[0] ? "YES" : "no");
  if (B[0]) {
    printf("  lexfirst:");
    uint32_t U = 0;
    while (U != T)
      for (int y = 1; y <= k; y++)
        if (!(U >> (y - 1) & 1) && valid(U, y) && B[U | 1u << (y - 1)]) {
          printf(" %d", y); U |= 1u << (y - 1); break;
        }
  }
  printf("\n");
  fflush(stdout);
  free(B);
}
int main(int argc, char **argv) {
  int KMAX = atoi(argv[1]);
  char buf[64];
  for (int k = 1; k <= KMAX; k++) {
    K = k; bgfrom = 0;
    sprintf(buf, "I(%d)", k);
    solve(buf, k);
  }
  for (int n = 3; n <= KMAX + 2; n++) {
    K = n - 2; bgfrom = n + 1;
    sprintf(buf, "Q(%d)", n);
    solve(buf, n - 2);
  }
  return 0;
}

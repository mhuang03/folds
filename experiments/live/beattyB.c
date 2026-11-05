/* beattyB.c N: Conjecture B check.  For every Beatty window copy
     X = X(N,p,g) = { floor((rN+g)/p) : r = 1..p },  1 <= p < N,  2p-1-N <= g <= 0,
   test whether the complement [N] \ X is reachable from scratch (equivalently: every valid
   ordering of X extends to a full semi-symmetric fold sequence).  Also re-checks that X is
   a window copy via the doubling criterion  c~(2x-1) = 2c(x)-1.
   Prints "summary N copies bad". */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int N;
static uint32_t L[40], Rm[40];
static uint8_t *reach;
#define GET(s) ((reach[(s) >> 3] >> ((s) & 7)) & 1)
#define SET(s) (reach[(s) >> 3] |= 1 << ((s) & 7))
static int valid(uint32_t S, int m) {
  return __builtin_popcount(S & L[m]) == __builtin_popcount(S & Rm[m]);
}
int main(int argc, char **argv) {
  N = atoi(argv[1]);
  for (int m = 1; m <= N; m++) {
    int r = m - 1 < N - m ? m - 1 : N - m;
    L[m] = Rm[m] = 0;
    for (int d = 1; d <= r; d++) { L[m] |= 1u << (m - d - 1); Rm[m] |= 1u << (m + d - 1); }
  }
  uint64_t full = (1ull << N) - 1;
  reach = calloc((full >> 3) + 1, 1);
  SET(0);
  for (uint64_t S = 0; S <= full; S++) {
    if (!GET(S)) continue;
    for (int m = 1; m <= N; m++)
      if (!(S >> (m - 1) & 1) && valid((uint32_t)S, m)) SET(S | (1ull << (m - 1)));
  }
  int copies = 0, bad = 0, notcopy = 0;
  for (int p = 1; p < N; p++)
    for (int g = 2 * p - 1 - N; g <= 0; g++) {
      uint32_t X = 0;
      int x[64];
      for (int r = 1; r <= p; r++) {
        int v = (int)(((long)r * N + g + (long)p * N) / p) - N; /* floor for negative g */
        x[r] = v;
        X |= 1u << (v - 1);
      }
      /* copy criterion */
      int c[80] = {0};
      for (int y = 1; y <= N; y++) c[y] = c[y - 1] + ((X >> (y - 1)) & 1);
      int iscopy = 1;
      for (int r = 1; r <= p; r++) {
        int y = 2 * x[r] - 1, ct = y <= N ? c[y] : p + c[y - N];
        if (ct != 2 * r - 1) iscopy = 0;
      }
      if (!iscopy) { notcopy++; continue; }
      copies++;
      if (!GET((uint32_t)full ^ X)) {
        bad++;
        printf("bad %d p=%d g=%d\n", N, p, g);
      }
    }
  printf("summary N=%d copies=%d notcopy=%d bad=%d\n", N, copies, notcopy, bad);
  return 0;
}

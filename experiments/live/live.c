/* live.c: which short prefixes of semi-symmetric fold sequences can be completed.
   R = sets S (bitmask over panels 1..N, bit m-1) with g(S) > 0, i.e. reachable from the
   empty set by valid steps.  A valid prefix p extends iff [N] \ set(p) is in R
   (extends_iff_g_pos).  Usage: live N [k]  (k >= 3 also lists dead 3-prefixes). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int N;
static uint32_t L[40], Rm[40];
static uint8_t *reach;
static int valid(uint32_t S, int m) {
  return __builtin_popcount(S & L[m]) == __builtin_popcount(S & Rm[m]);
}
#define GET(s) ((reach[(s) >> 3] >> ((s) & 7)) & 1)
#define SET(s) (reach[(s) >> 3] |= 1 << ((s) & 7))
int main(int argc, char **argv) {
  N = atoi(argv[1]);
  int K = argc > 2 ? atoi(argv[2]) : 3;
  for (int m = 1; m <= N; m++) {
    int r = m - 1 < N - m ? m - 1 : N - m;
    L[m] = Rm[m] = 0;
    for (int d = 1; d <= r; d++) { L[m] |= 1u << (m - d - 1); Rm[m] |= 1u << (m + d - 1); }
  }
  uint64_t full = (1ull << N) - 1;
  reach = calloc((full >> 3) + 1, 1);
  SET(0);
  for (uint64_t S = 0; S <= full; S++) { /* supersets come later in increasing order */
    if (!GET(S)) continue;
    for (int m = 1; m <= N; m++)
      if (!(S >> (m - 1) & 1) && valid((uint32_t)S, m)) SET(S | (1ull << (m - 1)));
  }
  uint32_t F = (uint32_t)full;
  int dead1 = 0;
  for (int a = 1; a <= N; a++)
    if (!GET(F ^ (1u << (a - 1)))) { dead1++; printf("dead1 %d %d\n", N, a); }
  int dead2 = 0, tot2 = 0;
  for (int a = 1; a <= N; a++)
    for (int b = 1; b <= N; b++) {
      if (a == b) continue;
      uint32_t Sa = 1u << (a - 1);
      if (!valid(Sa, b)) continue;
      tot2++;
      if (!GET(F ^ Sa ^ (1u << (b - 1)))) { dead2++; printf("dead2 %d %d %d\n", N, a, b); }
    }
  int dead3 = 0, tot3 = 0;
  if (K >= 3)
    for (int a = 1; a <= N; a++)
      for (int b = 1; b <= N; b++) {
        if (a == b) continue;
        uint32_t Sa = 1u << (a - 1), Sb = Sa | 1u << (b - 1);
        if (!valid(Sa, b)) continue;
        for (int c = 1; c <= N; c++) {
          if (c == a || c == b || !valid(Sb, c)) continue;
          tot3++;
          if (!GET(F ^ Sb ^ (1u << (c - 1)))) { dead3++; printf("dead3 %d %d %d %d\n", N, a, b, c); }
        }
      }
  printf("summary N=%d dead1=%d T2=%d dead2=%d T3=%d dead3=%d\n", N, dead1, tot2, dead2, tot3,
         dead3);
  return 0;
}

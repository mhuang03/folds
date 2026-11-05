/* reach.c N out: dump the bitset R of sets reachable from scratch (bit S set iff the panel
   set S, bit m-1 = panel m, has a semi-symmetric ordering from scratch). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int N;
static uint32_t L[40], Rm[40];
static uint8_t *reach;
#define GET(s) ((reach[(s) >> 3] >> ((s) & 7)) & 1)
#define SET(s) (reach[(s) >> 3] |= 1 << ((s) & 7))
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
      if (!(S >> (m - 1) & 1) &&
          __builtin_popcount((uint32_t)S & L[m]) == __builtin_popcount((uint32_t)S & Rm[m]))
        SET(S | (1ull << (m - 1)));
  }
  FILE *f = fopen(argv[2], "wb");
  fwrite(reach, 1, (full >> 3) + 1, f);
  fclose(f);
  return 0;
}

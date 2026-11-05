/* copies.c N Rfile: enumerate all window copies X of [N] (copy criterion
   c~(2x-1) = 2c(x)-1 for x in X, experiments/live/PROOFS.txt 3.1), 2 <= |X| < N, and print
   "X mask p good" where good = 1 iff [N] \ X is reachable from scratch. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
  int N = atoi(argv[1]);
  uint64_t full = (1ull << N) - 1;
  uint8_t *reach = malloc((full >> 3) + 1);
  FILE *f = fopen(argv[2], "rb");
  if (fread(reach, 1, (full >> 3) + 1, f) != (full >> 3) + 1) return 1;
  fclose(f);
  for (uint64_t X = 1; X < full; X++) {
    int p = __builtin_popcountll(X);
    if (p < 2) continue;
    int c[80];
    c[0] = 0;
    for (int y = 1; y <= N; y++) c[y] = c[y - 1] + ((X >> (y - 1)) & 1);
    int ok = 1;
    for (int x = 1; x <= N && ok; x++) {
      if (!((X >> (x - 1)) & 1)) continue;
      int y = 2 * x - 1, ct = y <= N ? c[y] : p + c[y - N];
      if (ct != 2 * c[x] - 1) ok = 0;
    }
    if (!ok) continue;
    uint64_t Y = full ^ X;
    int good = (reach[Y >> 3] >> (Y & 7)) & 1;
    printf("%llu %d %d\n", (unsigned long long)X, p, good);
  }
  return 0;
}

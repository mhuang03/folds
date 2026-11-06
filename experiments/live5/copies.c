// copies.c N maxodd: all window copies X of [N] (X balanced around each of its elements),
// |X| >= 3, with at most maxodd odd elements and at least one; prints them.
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  int N = atoi(argv[1]), maxodd = atoi(argv[2]);
  for (long mask = 0; mask < (1L << N); mask++) {
    int in[80] = {0}, p = 0, od = 0;
    for (int i = 0; i < N; i++) if (mask >> i & 1) { in[i + 1] = 1; p++; if ((i + 1) & 1) od++; }
    if (p < 3 || od > maxodd || od == 0) continue;
    int ok = 1;
    for (int m = 1; m <= N && ok; m++) if (in[m]) {
      int r = (m - 1 < N - m) ? m - 1 : N - m, I = 0;
      for (int d = 1; d <= r; d++) I += in[m - d] - in[m + d];
      if (I) ok = 0;
    }
    if (!ok) continue;
    printf("p=%d:", p);
    for (int m = 1; m <= N; m++) if (in[m]) printf(" %d", m);
    printf("\n");
  }
  return 0;
}

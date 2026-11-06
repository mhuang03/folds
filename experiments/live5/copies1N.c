// copies1N.c N: window copies X of [N] (X balanced around each of its elements) containing
// 1 and N; prints those of odd size p (so that {1, p} is not dead by parity).
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  int N = atoi(argv[1]);
  long cnt = 0;
  for (long mask = 0; mask < (1L << (N - 2)); mask++) {
    int in[64] = {0};
    in[1] = in[N] = 1;
    int p = 2;
    for (int i = 0; i < N - 2; i++) if (mask >> i & 1) { in[i + 2] = 1; p++; }
    if (argc < 3 && p % 2 == 0) continue;
    int ok = 1;
    for (int m = 1; m <= N && ok; m++) if (in[m]) {
      int r = (m - 1 < N - m) ? m - 1 : N - m, I = 0;
      for (int d = 1; d <= r; d++) I += in[m - d] - in[m + d];
      if (I) ok = 0;
    }
    if (!ok) continue;
    cnt++;
    printf("p=%d:", p);
    for (int m = 1; m <= N; m++) if (in[m]) printf(" %d", m);
    printf("\n");
  }
  fprintf(stderr, "N=%d: %ld odd copies containing 1,N\n", N, cnt);
  return 0;
}

/* greedyc.c NMIN NMAX mode: the 'near' greedy (repeatedly place the valid panel closest to the
   centre c = (a + b)/2 of the removed interval [a, b]; ties: smaller panel first, or larger
   with tie = -1) on [N] \ [a, b].
   mode 1: adjacent pairs b = a + 1;  mode 2: all intervals;  mode 0: single points.
   Prints failures.  Prefix sums make each validity test O(1); O(N^3) per instance. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int N;
static int placed[4096];
static int cnt[4096]; /* prefix counts, recomputed lazily */
static int run(int a, int b, int tie) {
  int total = N - (b - a + 1);
  memset(placed, 0, sizeof(int) * (N + 2));
  for (int step = 0; step < total; step++) {
    cnt[0] = 0;
    for (int i = 1; i <= N; i++) cnt[i] = cnt[i - 1] + placed[i];
    int best = -1, bk = 1 << 30, bt = 0;
    for (int m = 1; m <= N; m++) {
      if (placed[m] || (m >= a && m <= b)) continue;
      int r = m - 1 < N - m ? m - 1 : N - m;
      int l = cnt[m - 1] - cnt[m - 1 - r], rr = cnt[m + r] - cnt[m];
      if (l != rr) continue;
      int k = abs(2 * m - a - b);
      if (k < bk || (k == bk && tie * m < bt)) { bk = k; best = m; bt = tie * m; }
    }
    if (best < 0) return 0;
    placed[best] = 1;
  }
  return 1;
}
int main(int argc, char **argv) {
  int NMIN = atoi(argv[1]), NMAX = atoi(argv[2]), mode = atoi(argv[3]);
  int tie = argc > 4 ? atoi(argv[4]) : 1;
  long fails = 0, tot = 0;
  for (N = NMIN; N <= NMAX; N++) {
    for (int a = 1; a <= N; a++) {
      int blo = mode == 0 ? a : (mode == 1 ? a + 1 : a);
      int bhi = mode == 0 ? a : (mode == 1 ? a + 1 : N);
      for (int b = blo; b <= bhi && b <= N; b++) {
        if (a == 1 && b == N) continue;
        tot++;
        if (!run(a, b, tie)) {
          fails++;
          if (fails < 30) printf("FAIL N=%d [%d,%d]\n", N, a, b);
        }
      }
    }
  }
  printf("mode %d tie %d N=%d..%d: %ld failures of %ld\n", mode, tie, NMIN, NMAX, fails, tot);
  return 0;
}

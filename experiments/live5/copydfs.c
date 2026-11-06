// copydfs.c N u v: all window copies X of [N] containing u and v (DFS with pruning: when a
// window [x - r, x + r] of an element x is complete, X must be balanced around x).
// Prints p = |X|, the preimages of u and v, and X.
#include <stdio.h>
#include <stdlib.h>
int N, U, V, in[200], cnt;
int reach(int m) { return (m - 1 < N - m) ? m - 1 : N - m; }
// elements whose window closes at position k: x with x + reach(x) == k
void dfs(int k) {
  if (k > N) {
    int p = 0, pu = 0, pv = 0;
    for (int m = 1; m <= N; m++) if (in[m]) { p++; if (m == U) pu = p; if (m == V) pv = p; }
    if (p < 3) return;
    cnt++;
    printf("p=%d (%d,%d):", p, pu, pv);
    for (int m = 1; m <= N; m++) if (in[m]) printf(" %d", m);
    printf("\n");
    return;
  }
  for (int b = 0; b <= 1; b++) {
    if ((k == U || k == V) && !b) continue;
    in[k] = b;
    int ok = 1;
    for (int x = 1; x <= k && ok; x++) if (in[x] && x + reach(x) == k) {
      int r = reach(x), I = 0;
      for (int d = 1; d <= r; d++) I += in[x - d] - in[x + d];
      if (I) ok = 0;
    }
    if (ok) dfs(k + 1);
  }
  in[k] = 0;
}
int main(int argc, char **argv) {
  N = atoi(argv[1]); U = atoi(argv[2]); V = atoi(argv[3]);
  dfs(1);
  fprintf(stderr, "%d copies\n", cnt);
  return 0;
}

// copyp.c N p lo hi [maxprint]: window copies f(1) = lo < ... < f(p) = hi of [p] in [N]
// (index constraints: left-type j: f(2j-1) <= 2f(j)-1 < f(2j); right-type mirrored), and
// whether each is inward.  Prints the inward ones (up to maxprint) and counts.
#include <stdio.h>
#include <stdlib.h>
int N, P, f[400], maxprint = 10, printed; long ncopy, nin;
int reach(int m) { return (m - 1 < N - m) ? m - 1 : N - m; }
int in[400];
int inward(void) {
  for (int m = 1; m <= N; m++) in[m] = 0;
  for (int j = 1; j <= P; j++) in[f[j]] = 1;
  int maxneg = 0, minpos = N + 1;
  for (int m = 1; m <= N; m++) {
    int r = reach(m), I = 0;
    for (int d = 1; d <= r; d++) I += in[m - d] - in[m + d];
    if (in[m]) { if (I) return -1; }
    else if (I < 0) maxneg = m;
    else if (I > 0 && m < minpos) minpos = m;
  }
  return maxneg < minpos;
}
// check constraints involving only indices <= j, newly involving j
int ok(int j) {
  int x = f[j];
  // type consistency
  if (2 * j <= P && 2 * x > N + 1) return 0;
  if (2 * j >= P + 2 && 2 * x < N + 1) return 0;
  // j as 2i-1 or 2i of a left-type i
  if (j % 2 == 1) { int i = (j + 1) / 2; if (i < j && 2 * i <= P && x > 2 * f[i] - 1) return 0; }
  else { int i = j / 2; if (2 * i <= P && x < 2 * f[i]) return 0; }
  // j right-type: arms counted from the left
  if (2 * j >= P + 2) {
    int jp = P + 1 - j;           // index from the right
    // left arm of x must contain exactly jp - 1 elements: f(j - jp + 1) >= 2x - N > f(j - jp)
    if (f[j - jp + 1] < 2 * x - N) return 0;
    if (j - jp >= 1 && f[j - jp] >= 2 * x - N) return 0;
  }
  // middle index (P odd)
  if (P % 2 == 1 && 2 * j == P + 1) {
    if (2 * x <= N + 1) { /* left type: needs f(P) <= 2x-1, checked at the end */ }
    else { if (f[1] < 2 * x - N) return 0; }
  }
  return 1;
}
void dfs(int j, int hi) {
  if (j == P) {
    f[P] = hi;
    if (!ok(P)) return;
    if (P % 2 == 1) { int x = f[(P + 1) / 2]; if (2 * x <= N + 1 && hi > 2 * x - 1) return; }
    // full check (left-type j with 2j-1 or 2j > P handled here)
    int w = inward();
    if (w < 0) return;
    ncopy++;
    if (w) { nin++; if (printed < maxprint) { printed++; printf("p=%d:", P);
      for (int k = 1; k <= P; k++) printf(" %d", f[k]); printf("\n"); } }
    return;
  }
  for (int x = f[j - 1] + 1; x < hi; x++) {
    f[j] = x;
    if (ok(j)) dfs(j + 1, hi);
  }
}
int main(int argc, char **argv) {
  N = atoi(argv[1]); P = atoi(argv[2]); f[1] = atoi(argv[3]); int hi = atoi(argv[4]);
  if (argc > 5) maxprint = atoi(argv[5]);
  if (P >= 2) dfs(2, hi);
  printf("N=%d p=%d copies %ld inward %ld\n", N, P, ncopy, nin);
  return 0;
}

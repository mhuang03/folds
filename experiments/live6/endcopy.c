// endcopy.c N u v [maxprint] [stopgood]: inward window copies X of [N] with min X = u,
// max X = v.  X is a window copy iff I_X(x) = 0 for x in X; inward iff every m outside X
// with I_X(m) < 0 lies left of every m outside X with I_X(m) > 0.  DFS over panels with
// interval pruning (the final I(m) lies in [partial - unknown, partial]).
// Extra arguments: panels required in X.
// Prints p = |X| and X; with stopgood = 1 stops at the first X with |X| odd != 7 or |X| <= 3.
#include <stdio.h>
#include <stdlib.h>
int N, U, V, in[400], req[400], maxprint = 20, printed, stopgood, done; long cnt; long byp[400];
int reach(int m) { return (m - 1 < N - m) ? m - 1 : N - m; }
static int good(int p) { return p <= 3 || (p % 2 == 1 && p != 7); }
void dfs(int k) {
  if (done) return;
  if (k > N) {
    int p = 0; for (int m = 1; m <= N; m++) p += in[m];
    cnt++; byp[p]++;
    if (printed < maxprint) { printed++; printf("p=%d:", p);
      for (int m = 1; m <= N; m++) if (in[m]) printf(" %d", m); printf("\n"); }
    if (stopgood && good(p)) done = 1;
    return;
  }
  for (int b = 0; b <= 1; b++) {
    if ((k == U || k == V || req[k]) && !b) continue;
    if ((k < U || k > V) && b) continue;
    in[k] = b;
    int ok = 1, maxneg = 0, minpos = N + 1;
    for (int m = 1; m <= N && ok; m++) {
      int r = reach(m);
      if (m - r > k) break;           // left arm not yet decided
      if (m > k) {                      // m itself undecided: only full-window info useful
        continue;
      }
      int I = 0, unk = 0;
      for (int d = 1; d <= r; d++) {
        I += in[m - d];
        if (m + d <= k) I -= in[m + d]; else unk++;
      }
      if (in[m]) { if (I < 0 || I - unk > 0) ok = 0; }
      else {
        if (I < 0 && m > maxneg) maxneg = m;
        if (I - unk > 0 && m < minpos) minpos = m;
      }
    }
    if (ok && maxneg < minpos) dfs(k + 1);
  }
  in[k] = 0;
}
int main(int argc, char **argv) {
  N = atoi(argv[1]); U = atoi(argv[2]); V = atoi(argv[3]);
  if (argc > 4) maxprint = atoi(argv[4]);
  if (argc > 5) stopgood = atoi(argv[5]);
  for (int i = 6; i < argc; i++) req[atoi(argv[i])] = 1;
  dfs(1);
  printf("total %ld:", cnt);
  for (int p = 0; p <= N; p++) if (byp[p]) printf(" p%d=%ld", p, byp[p]);
  printf("\n");
  return 0;
}

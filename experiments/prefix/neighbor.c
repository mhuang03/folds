/* neighbor.c: test the "neighbour rule" on all valid k-sequences:
 *   when x_j is placed, the earlier points inside its window are exactly
 *     - none, if x_j is below or above all earlier points;
 *     - its two immediate neighbours (one on each side), otherwise.
 * usage: neighbor K Nmin Nmax ; prints N, T(N,K), and the number of violating sequences
 * (a sequence violates if some step violates).  Also counts violations by step type. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned long long u64;
static int N, K, X[16], used[1024];
static u64 tot, bad;
static int inwin(int x, int m){ int r = m-1 < N-m ? m-1 : N-m; int d = x > m ? x-m : m-x; return d <= r; }
static int rule_ok(int d, int m){ /* step d places m after X[0..d-1] */
  int lo = 0, hi = 0, L = -1, R = 1 << 30;
  for (int i = 0; i < d; i++){ if (X[i] < m){ lo++; if (X[i] > L) L = X[i]; } else { hi++; if (X[i] < R) R = X[i]; } }
  for (int i = 0; i < d; i++){
    int should = (lo && hi) && (X[i] == L || X[i] == R);
    if (inwin(X[i], m) != should) return 0; }
  return 1;
}
static void dfs(int d, int okk){
  if (d == K){ tot++; if (!okk) bad++; return; }
  for (int m = 1; m <= N; m++){ if (used[m]) continue;
    int l = 0, r = 0; for (int i = 0; i < d; i++) if (inwin(X[i], m)){ if (X[i] < m) l++; else r++; }
    if (l != r) continue;
    int o = okk && rule_ok(d, m);
    X[d] = m; used[m] = 1; dfs(d+1, o); used[m] = 0; }
}
int main(int argc, char **argv){
  K = atoi(argv[1]); int a = atoi(argv[2]), b = atoi(argv[3]);
  for (N = a; N <= b; N++){ tot = bad = 0; dfs(0, 1);
    printf("%d %llu %llu\n", N, tot, bad); fflush(stdout); }
}

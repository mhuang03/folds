/* copies.c: enumerate all window copies X of [N] (X balanced around each of its elements).
   usage: copies N            -> prints "N k count" for k = 1..N
          copies N c K        -> the count for size K only
          copies N list [K]   -> prints
                               "N k mask" (hex, bit m-1 = panel m; N <= 64).
   DFS left to right over the indicator x_1..x_N with the size s fixed, using the prefix form
     left half  (2m-1 <= N): P(2m-1) = P(m-1) + P(m)          (checked at t = 2m-1)
     right half (2m-1 >  N): P(m-1) - P(2m-1-N) = s - P(m)     (checked at t = m)
   with pruning on the pending left targets and on the total size. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
static int N, s, list;
static int P[400], x[400], req[400];
static long long cnt;
static void dfs(int t) { /* decide x_t; P[t-1] known */
  if (t > N) {
    if (P[N] == s) {
      cnt++;
      if (list) {
        uint64_t lo = 0;
        for (int i = 1; i <= N; i++) if (x[i]) lo |= 1ULL << (i - 1);
        printf("%d %d %llx\n", N, s, (unsigned long long)lo);
      }
    }
    return;
  }
  for (int v = 0; v <= 1; v++) {
    x[t] = v; P[t] = P[t - 1] + v;
    if (P[t] > s || P[t] + (N - t) < s) continue;
    if (req[t] >= 0 && req[t] != P[t]) continue;
    int ok = 1, setreq = -1;
    if (v) {
      int m = t;
      if (2 * m - 1 <= N) {
        int T = P[m - 1] + P[m], tt = 2 * m - 1;
        if (tt == m) { /* m = 1: empty window */ }
        else if (req[tt] >= 0 && req[tt] != T) ok = 0;
        else if (T < P[t] || T > P[t] + (tt - t)) ok = 0;
        else if (req[tt] < 0) setreq = tt;
      } else if (P[m - 1] - P[2 * m - 1 - N] != s - P[m]) ok = 0;
    }
    if (!ok) continue;
    int bad = 0;
    for (int u = t + 1; u <= N; u++)
      if (req[u] >= 0 && (req[u] < P[t] || req[u] > P[t] + (u - t))) { bad = 1; break; }
    if (bad) continue;
    if (setreq >= 0) req[setreq] = P[t - 1] + P[t];
    dfs(t + 1);
    if (setreq >= 0) req[setreq] = -1;
  }
}
int main(int argc, char **argv) {
  N = atoi(argv[1]); list = argc > 2 && argv[2][0] != 'c';
  int s0 = 1, s1 = N;
  if (argc > 3) { s0 = s1 = atoi(argv[3]); }
  for (s = s0; s <= s1; s++) {
    for (int i = 0; i < 400; i++) req[i] = -1;
    cnt = 0; P[0] = 0; dfs(1);
    if (!list) printf("%d %d %lld\n", N, s, cnt);
    fflush(stdout);
  }
  return 0;
}

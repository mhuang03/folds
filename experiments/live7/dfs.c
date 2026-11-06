/* dfs.c N u v [seed] [limit]: search a full semi-symmetric sequence of [N] starting with u, v
   (equivalently, reversed after dropping u, v: an ordering of [N] \ {u, v} from scratch).
   DFS with the pruning "every unplaced panel can still be balanced", random tie breaking,
   restarts after `limit` nodes.  Prints the completion (without u, v) on success. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int N, placed[300], seq[300], len;
static long nodes, limit;
static int rch(int m) { return m - 1 < N - m ? m - 1 : N - m; }
static int imb(int m) { /* left - right among placed */
  int r = rch(m), s = 0;
  for (int d = 1; d <= r; d++) s += placed[m - d] - placed[m + d];
  return s;
}
static int feasible(void) {
  for (int m = 1; m <= N; m++) {
    if (placed[m]) continue;
    int r = rch(m), L = 0, R = 0, fl = 0, fr = 0;
    for (int d = 1; d <= r; d++) {
      if (placed[m - d]) L++; else fl++;
      if (placed[m + d]) R++; else fr++;
    }
    if (L > R && L - R > fr) return 0;
    if (R > L && R - L > fl) return 0;
  }
  return 1;
}
static unsigned rng = 1;
static unsigned rnd(void) { rng = rng * 1103515245u + 12345u; return rng >> 8; }
static int dfs(void) {
  if (len == N) return 1;
  if (++nodes > limit) return 0;
  int c[300], k = 0;
  for (int m = 1; m <= N; m++) if (!placed[m] && imb(m) == 0) c[k++] = m;
  /* shuffle, then prefer far from the middle */
  for (int i = k - 1; i > 0; i--) { int j = rnd() % (i + 1), t = c[i]; c[i] = c[j]; c[j] = t; }
  for (int i = 0; i < k; i++) {
    int m = c[i];
    placed[m] = 1; seq[len++] = m;
    if (feasible() && dfs()) return 1;
    placed[m] = 0; len--;
    if (nodes > limit) return 0;
  }
  return 0;
}
int main(int argc, char **argv) {
  N = atoi(argv[1]);
  int u = atoi(argv[2]), v = atoi(argv[3]);
  rng = argc > 4 ? atoi(argv[4]) : 1;
  limit = argc > 5 ? atol(argv[5]) : 200000;
  for (int t = 0; t < 1000; t++) {
    memset(placed, 0, sizeof placed);
    len = 0; nodes = 0;
    placed[u] = placed[v] = 1; seq[len++] = u; seq[len++] = v;
    if (dfs()) {
      for (int i = 2; i < N; i++) printf("%d%c", seq[i], i + 1 < N ? ',' : '\n');
      fprintf(stderr, "restarts %d\n", t);
      return 0;
    }
  }
  printf("FAIL\n");
  return 1;
}

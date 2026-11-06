/* reach4.c -- for fixed size s (<= 6), the max of V(S) over all S and over REACHABLE S
   (S is the panel set of a valid prefix: some ordering of S is semi-symmetric).
   usage: ./reach4 N s */
#include <stdio.h>
#include <stdlib.h>
int N, s, in[512], P[512], cur[16];
int bestAll = -1, bestR = -1, bAll[16], bR[16];
int valid_m(int m) { /* free m valid w.r.t. current in[] */
  P[0] = 0; for (int j = 1; j <= N; j++) P[j] = P[j - 1] + in[j];
  int tot = P[N]; int j = 2 * m - 1; int pt = P[j % N] + (j / N) * tot;
  return pt == 2 * P[m - 1]; }
int cnt(void) { int V = 0; for (int m = 1; m <= N; m++) if (!in[m] && valid_m(m)) V++; return V; }
int reachable(int depth, int used) { /* can the elements of cur not in `used` be added in some valid order? */
  if (depth == s) return 1;
  for (int i = 0; i < s; i++) { if (used >> i & 1) continue; int m = cur[i];
    if (valid_m(m)) { in[m] = 1; int r = reachable(depth + 1, used | 1 << i); in[m] = 0; if (r) return 1; } }
  return 0; }
void rec(int i, int lo) {
  if (i == s) { int V = cnt();
    if (V > bestAll) { bestAll = V; for (int k = 0; k < s; k++) bAll[k] = cur[k]; }
    if (V > bestR) { for (int k = 0; k < s; k++) in[cur[k]] = 0;
      int r = reachable(0, 0); for (int k = 0; k < s; k++) in[cur[k]] = 1;
      if (r) { bestR = V; for (int k = 0; k < s; k++) bR[k] = cur[k]; } }
    return; }
  for (int x = lo; x <= N; x++) { cur[i] = x; in[x] = 1; rec(i + 1, x + 1); in[x] = 0; } }
int main(int argc, char **argv) { N = atoi(argv[1]); s = atoi(argv[2]); rec(0, 1);
  printf("N=%d s=%d floor(2N/3)=%d  all: %d {", N, s, 2 * N / 3, bestAll);
  for (int k = 0; k < s; k++) printf(" %d", bAll[k]);
  printf(" }  reachable: %d {", bestR); for (int k = 0; k < s; k++) printf(" %d", bR[k]); printf(" }\n"); return 0; }

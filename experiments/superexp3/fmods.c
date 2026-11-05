/* Contribution of a single half-time set X to F(N) = #{tau in V_N : k before 2k mod* N, all k}
   (and to a(N) when mode = 0):  f(X) * b(X), by DP over subsets of X and of X^c only.
   Usage: fmods N mode list-of-X-elements...      (prints f, b, f*b)
          fmods N mode -single                    (all X = odds Δ {u, v}, |u - v| <= 3) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int N, mode;
static int pred[80][80]; /* pred[y][x] = 1 : x must precede y */
static double run(int *el, int ne, int *base, int nb) {
  /* count orderings of el (indices into panels) with base panels already placed */
  static int placed[80];
  memset(placed, 0, sizeof placed);
  for (int i = 0; i < nb; i++) placed[base[i]] = 1;
  size_t NS = (size_t)1 << ne; double *c = calloc(NS, sizeof(double)); c[0] = 1;
  for (size_t S = 0; S < NS; S++) if (c[S]) {
    for (int i = 0; i < ne; i++) placed[el[i]] = S >> i & 1;
    for (int i = 0; i < ne; i++) { if (S >> i & 1) continue; int m = el[i];
      int okp = 1; for (int x = 1; x <= N && okp; x++) if (pred[m][x] && !placed[x]) okp = 0;
      if (!okp) continue;
      int r = m - 1 < N - m ? m - 1 : N - m, l = 0, rr = 0;
      for (int d = 1; d <= r; d++) { l += placed[m - d]; rr += placed[m + d]; }
      if (l == rr) c[S | 1u << i] += c[S]; }
  }
  double v = c[NS - 1]; free(c); return v;
}
static double contrib(int *inX, double *pf, double *pb) {
  int el[80], ne = 0, co[80], nc = 0;
  for (int y = 1; y <= N; y++) if (inX[y]) el[ne++] = y; else co[nc++] = y;
  /* a constraint x before y with x not in X, y in X is impossible */
  for (int y = 1; y <= N; y++) for (int x = 1; x <= N; x++) if (pred[y][x] && inX[y] && !inX[x]) { *pf = *pb = 0; return 0; }
  *pf = run(el, ne, NULL, 0); if (*pf == 0) { *pb = 0; return 0; }
  *pb = run(co, nc, el, ne); return *pf * *pb;
}
int main(int argc, char **argv) {
  N = atoi(argv[1]); mode = atoi(argv[2]);
  if (mode) for (int k = 1; k < N; k++) { int q = (2 * k - 1) % N + 1; pred[q][k] = 1; }
  int inX[80]; double f, b;
  if (argc > 3 && !strcmp(argv[3], "-single")) {
    memset(inX, 0, sizeof inX); for (int y = 1; y <= N; y += 2) inX[y] = 1;
    double base = contrib(inX, &f, &b);
    printf("odds: f=%.0f b=%.0f fb=%.0f\n", f, b, base);
    double tot = 0;
    for (int u = 1; u <= N; u++) for (int v = 1; v <= N; v++) {
      if (!(u % 2 == 0 && v % 2 == 1)) continue; if (abs(u - v) > 3) continue;
      memset(inX, 0, sizeof inX); for (int y = 1; y <= N; y += 2) inX[y] = 1; inX[u] = 1; inX[v] = 0;
      double c = contrib(inX, &f, &b); tot += c;
      if (c > 0) printf("  +%d -%d : f=%.0f b=%.0f ratio=%.4f\n", u, v, f, b, c / base);
    }
    printf("sum of single-swap ratios: %.4f\n", tot / base);
    return 0;
  }
  memset(inX, 0, sizeof inX); for (int i = 3; i < argc; i++) inX[atoi(argv[i])] = 1;
  double c = contrib(inX, &f, &b); printf("f=%.0f b=%.0f fb=%.0f\n", f, b, c);
  return 0;
}

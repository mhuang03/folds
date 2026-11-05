/* Subset DP with precedence constraints (as pdp.c), forward and backward; prints, for the
   sets X of size n/2 (the set placed at half time), f(X) * b(X), sorted.
   Usage: midset n mode [top]   mode as in superexp2/pdp.c (5 = G ⊇ odds). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n;
static unsigned pred[40];
static int ms(int x) { return ((x - 1) % n + n) % n + 1; }
static int ok(unsigned S, int m) {
  int r = m - 1 < n - m ? m - 1 : n - m;
  unsigned L = r ? (((1u << r) - 1) << (m - 1 - r)) : 0;
  unsigned R = r ? (((1u << r) - 1) << m) : 0;
  return __builtin_popcount(S & L) == __builtin_popcount(S & R);
}
typedef struct { unsigned X; double v; } E;
static int cmp(const void *a, const void *b) { double x = ((E*)a)->v, y = ((E*)b)->v; return x < y ? 1 : x > y ? -1 : 0; }
int main(int argc, char **argv) {
  n = atoi(argv[1]); int mode = atoi(argv[2]); int top = argc > 3 ? atoi(argv[3]) : 30;
  for (int k = 1; k <= n - 1; k++) {
    if ((mode & 4) && k % 2 == 0) continue;
    if (mode & 1) { int q = ms(2 * k); pred[q] |= 1u << (k - 1); }
    if (mode & 2) { int p = ms(2 * k + 1); pred[k + 1] |= 1u << (p - 1); }
  }
  size_t NS = (size_t)1 << n;
  double *f = calloc(NS, sizeof(double)), *b = calloc(NS, sizeof(double));
  f[0] = 1;
  for (size_t S = 0; S < NS; S++) if (f[S])
    for (int m = 1; m <= n; m++) { unsigned bit = 1u << (m - 1);
      if ((S & bit) || (pred[m] & S) != pred[m] || !ok(S, m)) continue; f[S | bit] += f[S]; }
  b[NS - 1] = 1;
  for (size_t S = NS - 1; S-- > 0;) { double v = 0;
    for (int m = 1; m <= n; m++) { unsigned bit = 1u << (m - 1);
      if ((S & bit) || (pred[m] & S) != pred[m] || !ok(S, m)) continue; v += b[S | bit]; }
    b[S] = v; }
  printf("total %.0f\n", f[NS - 1]);
  E *e = malloc(NS * sizeof(E)); size_t ne = 0; double tot = 0;
  for (size_t S = 0; S < NS; S++) if (__builtin_popcount(S) == n / 2 && f[S] * b[S] > 0) {
    e[ne].X = S; e[ne].v = f[S] * b[S]; tot += e[ne].v; ne++; }
  qsort(e, ne, sizeof(E), cmp);
  printf("%zu sets, sum %.0f\n", ne, tot);
  for (size_t i = 0; i < ne && i < (size_t)top; i++) {
    printf("%12.0f  f=%10.0f b=%10.0f  ", e[i].v, f[e[i].X], b[e[i].X]);
    for (int m = 1; m <= n; m++) putchar(e[i].X >> (m - 1) & 1 ? 'x' : '.');
    putchar('\n'); }
  return 0;
}

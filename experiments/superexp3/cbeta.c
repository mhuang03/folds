/* c(beta) = #{tau in V_{2m} : G(tau) ⊇ odds, the even panels appear in the order 2*beta}
   for every valid beta in V_m (or a sample).  Prints min / mean / max of c(beta)/a(m).
   (The chain uses only tau = PB(alpha, beta): c(beta) >= a(m).)
   Usage: cbeta m [mode] [sample]   mode 1: require G(tau) = everything (F-type) instead */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n, m;
static int okm(unsigned S, int x, int nn) {
  int r = x - 1 < nn - x ? x - 1 : nn - x;
  unsigned L = r ? (((1u << r) - 1) << (x - 1 - r)) : 0;
  unsigned R = r ? (((1u << r) - 1) << x) : 0;
  return __builtin_popcount(S & L) == __builtin_popcount(S & R);
}
static int *V; static int nv = 0, cap = 0, cur[32];
static void gen(int k, unsigned S) {
  if (k == m) { if (nv == cap) { cap = cap ? 2 * cap : 64; V = realloc(V, (size_t)cap * m * sizeof(int)); }
    memcpy(V + (size_t)nv * m, cur, m * sizeof(int)); nv++; return; }
  for (int x = 1; x <= m; x++) if (!(S >> (x - 1) & 1) && okm(S, x, m)) { cur[k] = x; gen(k + 1, S | 1u << (x - 1)); }
}
int main(int argc, char **argv) {
  m = atoi(argv[1]); n = 2 * m; int mode = argc > 2 ? atoi(argv[2]) : 0; int sample = argc > 3 ? atoi(argv[3]) : 0;
  gen(0, 0);
  unsigned base[64]; memset(base, 0, sizeof base);
  for (int k = 1; k < n; k++) { if (!mode && k % 2 == 0) continue; int q = (2 * k - 1) % n + 1; base[q] |= 1u << (k - 1); }
  size_t NS = (size_t)1 << n; double *c = malloc(NS * sizeof(double));
  double mn = 1e300, mx = 0, sum = 0; int cnt = 0;
  srand(7);
  int tot = sample ? sample : nv;
  for (int it = 0; it < tot; it++) {
    int bi = sample ? rand() % nv : it; int *b = V + (size_t)bi * m;
    unsigned pred[64]; memcpy(pred, base, sizeof pred);
    for (int i = 1; i < m; i++) pred[2 * b[i]] |= 1u << (2 * b[i - 1] - 1);
    memset(c, 0, NS * sizeof(double)); c[0] = 1;
    for (size_t S = 0; S < NS; S++) if (c[S])
      for (int x = 1; x <= n; x++) { unsigned bit = 1u << (x - 1);
        if ((S & bit) || (pred[x] & S) != pred[x] || !okm(S, x, n)) continue; c[S | bit] += c[S]; }
    double v = c[NS - 1] / nv; sum += v; cnt++; if (v < mn) mn = v; if (v > mx) mx = v;
  }
  printf("m=%d mode=%d: c(beta)/a(m): min %.4f mean %.4f max %.4f  (%d betas)\n", m, mode, mn, sum / cnt, mx, cnt);
  return 0;
}

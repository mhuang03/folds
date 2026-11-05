/* Extra slips paid for by the FREE halves of the chain.
   Top size 2n = 4m.  tau = PB(alpha, beta), sigma = PB(alpha', beta') (odds-first).
   Count the sets X (general slip lemma) whose T-pairs are free (odd before even) or inside alpha
   (odd-odd), and whose S-pairs are free or inside beta' (even-even): these are certified
   without touching the coupled halves beta, alpha'.
   W(alpha, beta') = #{such X certified}.  Prints sum W / a(m)^2 and E log2 W, versus m
   (the m free odd-k slips alone give W >= 2^m).  Usage: freehalf m */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
static int n, N, m;
static int okm(unsigned S, int x, int nn) {
  int r = x - 1 < nn - x ? x - 1 : nn - x;
  unsigned L = r ? (((1u << r) - 1) << (x - 1 - r)) : 0;
  unsigned R = r ? (((1u << r) - 1) << x) : 0;
  return __builtin_popcount(S & L) == __builtin_popcount(S & R);
}
static int ms(int x) { return ((x - 1) % n + n) % n + 1; }
/* valid m-sequences as position arrays */
static int *P; static int nv = 0, cap = 0; static int cur[32];
static void gen(int k, unsigned S) {
  if (k == m) { if (nv == cap) { cap = cap ? 2 * cap : 64; P = realloc(P, (size_t)cap * 33 * sizeof(int)); }
    for (int i = 0; i < m; i++) P[nv * 33 + cur[i]] = i; nv++; return; }
  for (int x = 1; x <= m; x++) if (!(S >> (x - 1) & 1) && okm(S, x, m)) { cur[k] = x; gen(k + 1, S | 1u << (x - 1)); }
}
typedef struct { int na, nb; unsigned char a[64][2], b[64][2]; } C;
int main(int argc, char **argv) {
  m = atoi(argv[1]); n = 2 * m; N = 2 * n;
  gen(0, 0);
  C *cs = NULL; int ncs = 0, ccap = 0;
  int kap[200], f[100], s[100];
  for (unsigned long long M = 0; M < (1ULL << N); M++) {
    if (__builtin_popcountll(M) != n) continue;
    int nf = 0, ns = 0; kap[0] = 0;
    for (int y = 1; y <= N; y++) { int in = M >> (y - 1) & 1; kap[y] = kap[y - 1] + in; if (in) f[++nf] = y; else s[++ns] = y; }
    C c; c.na = c.nb = 0; int imp = 0;
    for (int j = 1; j <= n && !imp; j++)
      for (int w = 0; w < 2 && !imp; w++) {
        int yy = 2 * (w ? s[j] : f[j]) - 1; int qq = yy / N, r = yy % N;
        int kt = n * qq + kap[r]; int v = w ? yy - kt : kt;
        int lo = 2 * j - 1 < v ? 2 * j - 1 : v, hi = 2 * j - 1 < v ? v : 2 * j - 1;
        for (int y = lo + 1; y <= hi; y++) { int x = ms(y);
          if (x == j) { if (w) imp = 1; continue; }
          int a = w ? x : j, b = w ? j : x; /* a before b */
          if ((a & 1) && !(b & 1)) continue;           /* odd before even: free in odds-first */
          if (!(a & 1) && (b & 1)) { imp = 1; break; } /* even before odd: impossible */
          if (!w) { if (!(a & 1)) { imp = 1; break; }  /* even-even in tau: beta (coupled) */
                    if (c.na >= 64) { imp = 1; break; } c.a[c.na][0] = (a + 1) / 2; c.a[c.na][1] = (b + 1) / 2; c.na++; }
          else { if (a & 1) { imp = 1; break; }        /* odd-odd in sigma: alpha' (coupled) */
                 if (c.nb >= 64) { imp = 1; break; } c.b[c.nb][0] = a / 2; c.b[c.nb][1] = b / 2; c.nb++; } }
      }
    if (imp) continue;
    if (ncs == ccap) { ccap = ccap ? 2 * ccap : 1024; cs = realloc(cs, (size_t)ccap * sizeof(C)); }
    cs[ncs++] = c;
  }
  fprintf(stderr, "a(%d)=%d, %d candidate X\n", m, nv, ncs);
  /* per alpha: bitmask over candidates satisfied; same for beta' */
  int words = (ncs + 63) / 64;
  unsigned long long *A = calloc((size_t)nv * words, 8), *Bm = calloc((size_t)nv * words, 8);
  for (int i = 0; i < nv; i++) { int *p = P + i * 33;
    for (int k = 0; k < ncs; k++) { int ok = 1;
      for (int t = 0; t < cs[k].na && ok; t++) if (p[cs[k].a[t][0]] > p[cs[k].a[t][1]]) ok = 0;
      if (ok) A[(size_t)i * words + k / 64] |= 1ULL << (k % 64);
      ok = 1;
      for (int t = 0; t < cs[k].nb && ok; t++) if (p[cs[k].b[t][0]] > p[cs[k].b[t][1]]) ok = 0;
      if (ok) Bm[(size_t)i * words + k / 64] |= 1ULL << (k % 64); } }
  double sum = 0, slog = 0, mn = 1e300;
  for (int i = 0; i < nv; i++) for (int j = 0; j < nv; j++) {
    long W = 0; for (int w = 0; w < words; w++) W += __builtin_popcountll(A[(size_t)i * words + w] & Bm[(size_t)j * words + w]);
    sum += W; slog += log2((double)W); if (W < mn) mn = W; }
  double pairs = (double)nv * nv;
  printf("m=%d (top N=%d): E W = %.3f (2^m = %d), E log2 W = %.4f (m = %d), min W = %.0f; per m: E log2 W / m = %.4f\n",
         m, N, sum / pairs, 1 << m, slog / pairs, m, mn, slog / pairs / m);
  return 0;
}

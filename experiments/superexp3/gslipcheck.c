/* Exhaustive check of the general slip lemma (PROOFS.txt, Theorem 1).
   N = 2n, X an n-subset of [2n], f = sorted X, s = sorted complement, kappa = counting
   function of X, lambda(y) = y - kappa(y), both extended by kappa~(2n a + y) = n a + kappa(y).
   (A) induced conditions, for EVERY permutation tau / sigma of [n]:
       first block f_tau valid       <=>  for all steps j:  t~(kappa~(2 f_j - 1)) = 2 t(j - 1)
       second block s_sigma valid    <=>  for all steps j:  u~(lambda~(2 s_j - 1)) - 2 u(j-1)
                                                           = lambda~(2 s_j - 1) - (2j - 1)
       (t, u = counting functions of the indices placed before j, ~ = cyclic extension mod n)
   (B) for strip-valid tau, sigma: the interval form (no index of I_j placed before j in tau;
       every index of J_j, counted with multiplicity, placed before j in sigma).
   Usage: gslipcheck nmax [permmax]   (A) is run for n <= permmax (all n! permutations). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n, N;
static int kap[200], f[100], s[100];
static int kt(int y) { int a = y / N, r = y % N; return n * a + kap[r]; }
static int lt(int y) { return y - kt(y); }
static int ms(int x) { return ((x - 1) % n + n) % n + 1; }
/* direct validity in the N-strip of placing panel p given placed[] */
static int step_ok(int p, const int *placed) {
  int r = p - 1 < N - p ? p - 1 : N - p, l = 0, rr = 0;
  for (int d = 1; d <= r; d++) { l += placed[p - d]; rr += placed[p + d]; }
  return l == rr;
}
static int strip_ok(int x, const int *pl) { /* validity in the n-strip */
  int r = x - 1 < n - x ? x - 1 : n - x, l = 0, rr = 0;
  for (int d = 1; d <= r; d++) { l += pl[x - d]; rr += pl[x + d]; }
  return l == rr;
}
static int cyc(const int *pl, int y) { /* t~(y) for the placed set pl of [n] */
  int a = y / n, r = y % n, c = 0, tot = 0;
  for (int x = 1; x <= n; x++) { tot += pl[x]; if (x <= r) c += pl[x]; }
  return c + a * tot;
}
static long bad = 0, checks = 0;
static int perm[32], usedp[32];
static void check_perm(int full) {
  /* first block */
  int placed[200] = {0}, pl[64] = {0}, ok = 1, pred = 1, stripv = 1, predB = 1;
  for (int k = 0; k < n; k++) {
    int j = perm[k], p = f[j];
    int v = step_ok(p, placed);
    int lhs = cyc(pl, kt(2 * p - 1)), rhs = 2 * cyc(pl, j - 1);
    if (v != (lhs == rhs)) pred = 0;
    ok &= v;
    if (!strip_ok(j, pl)) stripv = 0;
    /* interval form */
    { int a = 2 * j - 1, b = kt(2 * p - 1), lo = a < b ? a : b, hi = a < b ? b : a;
      for (int y = lo + 1; y <= hi; y++) if (pl[ms(y)]) { if (ms(y) != j) predB = 0; } }
    placed[p] = 1; pl[j] = 1;
  }
  checks++;
  if (full && !pred) bad++;
  if (stripv && (ok != predB)) bad++;
  /* second block, on top of the complete first block */
  int placed2[200] = {0}, ul[64] = {0}, ok2 = 1, pred2 = 1, stripv2 = 1, predB2 = 1;
  for (int y = 1; y <= n; y++) placed2[f[y]] = 1;
  for (int k = 0; k < n; k++) {
    int j = perm[k], p = s[j];
    int v = step_ok(p, placed2);
    int L = lt(2 * p - 1);
    int lhs = cyc(ul, L) - 2 * cyc(ul, j - 1), rhs = L - (2 * j - 1);
    if (v != (lhs == rhs)) pred2 = 0;
    ok2 &= v;
    if (!strip_ok(j, ul)) stripv2 = 0;
    { int a = 2 * j - 1, lo = a < L ? a : L, hi = a < L ? L : a; int seen[64] = {0};
      for (int y = lo + 1; y <= hi; y++) { int x = ms(y); if (!ul[x] || seen[x]) predB2 = 0; seen[x] = 1; } }
    placed2[p] = 1; ul[j] = 1;
  }
  checks++;
  if (full && !pred2) bad++;
  if (stripv2 && (ok2 != predB2)) bad++;
}
static void rec(int k, int full) {
  if (k == n) { check_perm(full); return; }
  for (int x = 1; x <= n; x++) if (!usedp[x]) {
    if (!full) { /* prune to strip-valid sequences */
      int pl[64] = {0}; for (int i = 0; i < k; i++) pl[perm[i]] = 1;
      if (!strip_ok(x, pl)) continue; }
    usedp[x] = 1; perm[k] = x; rec(k + 1, full); usedp[x] = 0; }
}
int main(int argc, char **argv) {
  int nmax = atoi(argv[1]), permmax = argc > 2 ? atoi(argv[2]) : 0;
  for (n = 1; n <= nmax; n++) {
    N = 2 * n; bad = checks = 0; long nX = 0;
    for (unsigned long long M = 0; M < (1ULL << N); M++) {
      if (__builtin_popcountll(M) != n) continue; nX++;
      int nf = 0, ns = 0; kap[0] = 0;
      for (int y = 1; y <= N; y++) { int in = M >> (y - 1) & 1; kap[y] = kap[y - 1] + in; if (in) f[++nf] = y; else s[++ns] = y; }
      memset(usedp, 0, sizeof usedp); rec(0, n <= permmax);
    }
    printf("n=%d: %ld sets X, %ld block checks (%s), failures %ld\n", n, nX, checks,
           n <= permmax ? "all permutations" : "strip-valid blocks", bad);
    fflush(stdout);
  }
  return 0;
}

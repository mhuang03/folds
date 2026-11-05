/* Free general slips over residue-class block sequences.
   N = 2n, q | n.  tau, sigma in V_n are residue-class block sequences mod q: the classes
   r = 1..q (class r = {x ≡ r mod q}, class q = multiples) are placed in the order of a valid
   q-sequence, each class in the order of an arbitrary valid (n/q)-sequence (composition theorem).
   For every n-set X of [2n] (general slip lemma, gslip.py) count the pairs of class orders
   (o_tau, o_sigma) for which every T-pair and S-pair joins two different classes in the right
   order ("free": certified for all inner orders).  Prints
      C_free(n) = sum_X #{(o_tau, o_sigma) free for X}
   so that a(2n) >= C_free(n) * a(n/q)^{2q}.  Usage: freeq n q */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n, N, q;
static int ord[64][8]; static int nord = 0; /* rank of each class in each valid q-sequence */
static int okm(unsigned S, int m, int nn) {
  int r = m - 1 < nn - m ? m - 1 : nn - m;
  unsigned L = r ? (((1u << r) - 1) << (m - 1 - r)) : 0;
  unsigned R = r ? (((1u << r) - 1) << m) : 0;
  return __builtin_popcount(S & L) == __builtin_popcount(S & R);
}
static int cur[8];
static void genq(int k, unsigned S) {
  if (k == q) { for (int i = 0; i < q; i++) ord[nord][cur[i] % q] = i; nord++; return; }
  for (int m = 1; m <= q; m++) if (!(S >> (m - 1) & 1) && okm(S, m, q)) { cur[k] = m; genq(k + 1, S | 1u << (m - 1)); }
}
static int ms(int x) { return ((x - 1) % n + n) % n + 1; }
int main(int argc, char **argv) {
  n = atoi(argv[1]); q = atoi(argv[2]); N = 2 * n;
  genq(0, 0);
  double total = 0; long nX = 0; int kap[200], f[100], s[100];
  static int ta[100000], tb[100000], sa[100000], sb[100000];
  double hist[64] = {0};
  for (unsigned long long M = 0; M < (1ULL << N); M++) {
    if (__builtin_popcountll(M) != n) continue;
    int nf = 0, ns = 0; kap[0] = 0;
    for (int y = 1; y <= N; y++) { int in = M >> (y - 1) & 1; kap[y] = kap[y - 1] + in; if (in) f[++nf] = y; else s[++ns] = y; }
    int npt = 0, nps = 0, imp = 0;
    for (int j = 1; j <= n && !imp; j++)
      for (int w = 0; w < 2 && !imp; w++) {
        int yy = 2 * (w ? s[j] : f[j]) - 1; int qq = yy / N, r = yy % N;
        int kt = n * qq + kap[r]; int v = w ? yy - kt : kt;
        int lo = 2 * j - 1 < v ? 2 * j - 1 : v, hi = 2 * j - 1 < v ? v : 2 * j - 1;
        for (int y = lo + 1; y <= hi; y++) { int x = ms(y);
          if (x == j) { if (w) imp = 1; continue; }
          /* any same-class pair is not free */
          if ((x - j) % q == 0) { imp = 1; break; }
          if (!w) { ta[npt] = j; tb[npt++] = x; } else { sa[nps] = x; sb[nps++] = j; } }
      }
    if (imp) continue;
    double ct = 0, cs = 0;
    for (int o = 0; o < nord; o++) {
      int okt = 1, oks = 1;
      for (int k = 0; k < npt && okt; k++) if (ord[o][ta[k] % q] > ord[o][tb[k] % q]) okt = 0;
      for (int k = 0; k < nps && oks; k++) if (ord[o][sa[k] % q] > ord[o][sb[k] % q]) oks = 0;
      ct += okt; cs += oks;
    }
    if (ct * cs > 0) { total += ct * cs; nX++; }
  }
  printf("n=%d q=%d: %d class orders, C_free = %.0f over %ld sets X;  log2 C_free / n = %.4f\n",
         n, q, nord, total, nX, total > 0 ? __builtin_log2(total) / n : 0);
  return 0;
}

/* Generalized slip sums (general slip lemma, gslip.py).  N = 2n.
   For every n-set X of [2n]: precedence systems for tau (T) and sigma (S) from the intervals
   I_j, J_j; count
     T(X) = #{tau in V_n : T-conditions},  S(X) likewise, and the parity-block versions
     TP(X) = #{tau = PB in either orientation : T-conditions} (n even).
   Prints  sum_X T S / a(n)^2  (all of a(2n) obtainable from strip-valid blocks),
           sum_X TP SP / a(n/2)^4,  and the number of X contributing.
   Usage: gsum n [maxdisc]   (maxdisc: only X with max |kappa(y) - y/2| <= maxdisc/2) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n, N;
static double *cbuf;
static int okm(unsigned S, int m, int nn) {
  int r = m - 1 < nn - m ? m - 1 : nn - m;
  unsigned L = r ? (((1u << r) - 1) << (m - 1 - r)) : 0;
  unsigned R = r ? (((1u << r) - 1) << m) : 0;
  return __builtin_popcount(S & L) == __builtin_popcount(S & R);
}
static double count(unsigned *pred, int nn) {
  size_t NS = (size_t)1 << nn; memset(cbuf, 0, NS * sizeof(double)); cbuf[0] = 1;
  for (size_t S = 0; S < NS; S++) if (cbuf[S])
    for (int m = 1; m <= nn; m++) { unsigned bit = 1u << (m - 1);
      if ((S & bit) || (pred[m] & S) != pred[m] || !okm(S, m, nn)) continue; cbuf[S | bit] += cbuf[S]; }
  return cbuf[NS - 1];
}
static int ms(int x) { return ((x - 1) % n + n) % n + 1; }
/* pairs a before b */
static int np; static int pa[4096], pb[4096];
static double countPB(void) {
  int m = n / 2; double tot = 0;
  for (int o = 0; o < 2; o++) { /* o = 0: odds first, 1: evens first */
    unsigned po[40], pe[40]; memset(po, 0, sizeof po); memset(pe, 0, sizeof pe); int bad = 0;
    for (int k = 0; k < np && !bad; k++) {
      int a = pa[k], b = pb[k];
      if ((a & 1) != (b & 1)) { int aodd = a & 1; if ((o == 0) != aodd) bad = 1; continue; }
      if (a & 1) po[(b + 1) / 2] |= 1u << ((a + 1) / 2 - 1);
      else pe[b / 2] |= 1u << (a / 2 - 1);
    }
    if (bad) continue;
    tot += count(po, m) * count(pe, m);
  }
  return tot;
}
int main(int argc, char **argv) {
  n = atoi(argv[1]); N = 2 * n; int maxdisc = argc > 2 ? atoi(argv[2]) : 1000; int pbonly = argc > 3 ? atoi(argv[3]) : 0;
  cbuf = malloc(((size_t)1 << n) * sizeof(double));
  unsigned z[40]; memset(z, 0, sizeof z);
  double a = pbonly ? 1 : count(z, n), am = n % 2 == 0 ? count(z, n / 2) : 1;
  double sumAll = 0, sumPB = 0; long nAll = 0, nPB = 0;
  int X[64], f[64], s[64], kap[130];
  /* enumerate n-subsets of [2n] as bitmasks */
  for (unsigned long long M = 0; M < (1ULL << N); M++) {
    if (__builtin_popcountll(M) != n) continue;
    int nf = 0, ns = 0, c = 0, mx = 0; kap[0] = 0;
    for (int y = 1; y <= N; y++) { int in = M >> (y - 1) & 1; X[y] = in; kap[y] = kap[y - 1] + in;
      if (in) f[++nf] = y; else s[++ns] = y;
      c += in ? 1 : -1; int ac = c < 0 ? -c : c; if (ac > mx) mx = ac; }
    if (mx > maxdisc) continue;
    unsigned pt[40], ps[40]; memset(pt, 0, sizeof pt); memset(ps, 0, sizeof ps);
    int imp = 0; int npt = 0, nps = 0; static int ta[4096], tb[4096], sa[4096], sb[4096];
    for (int j = 1; j <= n && !imp; j++) {
      for (int w = 0; w < 2 && !imp; w++) {
        int yy = 2 * (w ? s[j] : f[j]) - 1; int q = yy / N, r = yy % N;
        int kt = n * q + kap[r]; int v = w ? yy - kt : kt;
        int lo = 2 * j - 1 < v ? 2 * j - 1 : v, hi = 2 * j - 1 < v ? v : 2 * j - 1;
        if (hi - lo >= n && w) { imp = 1; break; }
        unsigned seen = 0;
        for (int y = lo + 1; y <= hi; y++) { int x = ms(y);
          if (!w) { if (x != j) { pt[x] |= 1u << (j - 1); ta[npt] = j; tb[npt++] = x; } }
          else { if (x == j || (seen >> (x - 1) & 1)) { imp = 1; break; } seen |= 1u << (x - 1);
                 ps[j] |= 1u << (x - 1); sa[nps] = x; sb[nps++] = j; } }
      }
    }
    if (imp) continue;
    /* cycles in pt make T zero automatically via DP */
    if (!pbonly) {
    double T = count(pt, n); if (T == 0) continue;
    double S = count(ps, n); if (S == 0) continue;
    sumAll += T * S; nAll++; }
    if (n % 2 == 0) {
      np = npt; memcpy(pa, ta, npt * sizeof(int)); memcpy(pb, tb, npt * sizeof(int));
      double TP = countPB();
      np = nps; memcpy(pa, sa, nps * sizeof(int)); memcpy(pb, sb, nps * sizeof(int));
      double SP = countPB();
      if (TP * SP > 0) { sumPB += TP * SP; nPB++; }
    }
  }
  printf("n=%d a(n)=%.0f  sum_X T S / a(n)^2 = %.4f (%ld X)", n, a, sumAll / (a * a), nAll);
  if (n % 2 == 0) printf("   PB: sum / a(n/2)^4 = %.4f (%ld X)", sumPB / (am * am * am * am), nPB);
  printf("\n");
  return 0;
}

/* Free general slips for ANY N (in particular odd N), first block size n1, second n2 = N - n1.
   General slip lemma for blocks of sizes n1, n2:  kappa~(N a + r) = n1 a + kappa(r),
   lambda~(N a + r) = n2 a + lambda(r);  tau in V_{n1} (indices mod n1), sigma in V_{n2}.
   tau, sigma are parity-block sequences (odds-first or evens-first, valid for every strip size).
   Counts the sets X (|X| = n1) all of whose T- and S-pairs join different parity classes in the
   right order for some orientation, weighted by the number of orientations (C_free), so that
   a(N) >= C_free * a(ceil(n1/2)) a(floor(n1/2)) a(ceil(n2/2)) a(floor(n2/2)).
   With -v, also verifies every produced sequence for small N by brute force (all inner orders).
   Usage: freeodd N n1 [-v] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int N, n1, n2;
static int ms(int x, int m) { return ((x - 1) % m + m) % m + 1; }
static int okm(const int *pl, int x, int nn) {
  int r = x - 1 < nn - x ? x - 1 : nn - x, l = 0, rr = 0;
  for (int d = 1; d <= r; d++) { l += pl[x - d]; rr += pl[x + d]; }
  return l == rr;
}
/* enumerate parity-block sequences of [m] (both orientations, all valid inner orders) */
static int nseq[2]; static int seqs[2][200000][16];
static int cur[16];
static int inner[2][4096][16]; static int ninner[2];
static void geninner(int m, int k, int *pl, int which) {
  if (k == m) { memcpy(inner[which][ninner[which]++], cur, sizeof cur); return; }
  for (int x = 1; x <= m; x++) if (!pl[x] && okm(pl, x, m)) { pl[x] = 1; cur[k] = x; geninner(m, k + 1, pl, which); pl[x] = 0; }
}
static void genPB(int m, int slot) {
  int mo = (m + 1) / 2, me = m / 2; int pl[40];
  ninner[0] = ninner[1] = 0;
  memset(pl, 0, sizeof pl); geninner(mo, 0, pl, 0);
  memset(pl, 0, sizeof pl); geninner(me, 0, pl, 1);
  nseq[slot] = 0;
  for (int o = 0; o < 2; o++) for (int a = 0; a < ninner[0]; a++) for (int b = 0; b < ninner[1]; b++) {
    int *s = seqs[slot][nseq[slot]++], k = 0;
    if (o == 0) { for (int i = 0; i < mo; i++) s[k++] = 2 * inner[0][a][i] - 1; for (int i = 0; i < me; i++) s[k++] = 2 * inner[1][b][i]; }
    else { for (int i = 0; i < me; i++) s[k++] = 2 * inner[1][b][i]; for (int i = 0; i < mo; i++) s[k++] = 2 * inner[0][a][i] - 1; }
  }
}
int main(int argc, char **argv) {
  N = atoi(argv[1]); n1 = atoi(argv[2]); n2 = N - n1; int verify = argc > 3;
  if (verify) { genPB(n1, 0); genPB(n2, 1); }
  double total = 0; long nX = 0, vbad = 0, vgood = 0; int kap[200], f[100], s[100];
  static int ta[10000], tb[10000], sa[10000], sb[10000];
  for (unsigned long long M = 0; M < (1ULL << N); M++) {
    if (__builtin_popcountll(M) != n1) continue;
    int nf = 0, ns = 0; kap[0] = 0;
    for (int y = 1; y <= N; y++) { int in = M >> (y - 1) & 1; kap[y] = kap[y - 1] + in; if (in) f[++nf] = y; else s[++ns] = y; }
    int npt = 0, nps = 0, imp = 0;
    for (int w = 0; w < 2 && !imp; w++) {
      int nb = w ? n2 : n1;
      for (int j = 1; j <= nb && !imp; j++) {
        int yy = 2 * (w ? s[j] : f[j]) - 1; int qq = yy / N, r = yy % N;
        int kt = n1 * qq + kap[r]; int v = w ? yy - kt : kt;
        int lo = 2 * j - 1 < v ? 2 * j - 1 : v, hi = 2 * j - 1 < v ? v : 2 * j - 1;
        for (int y = lo + 1; y <= hi; y++) { int x = ms(y, nb);
          if (x == j) { if (w) imp = 1; continue; }
          if ((x - j) % 2 == 0) { imp = 1; break; }
          if (!w) { ta[npt] = j; tb[npt++] = x; } else { sa[nps] = x; sb[nps++] = j; } }
      }
    }
    if (imp) continue;
    int ct = 0, cs = 0, okt[2], oks[2];
    for (int o = 0; o < 2; o++) { /* o = 0: odds first */
      okt[o] = oks[o] = 1;
      for (int k = 0; k < npt; k++) if (((ta[k] & 1) == 1) != (o == 0)) okt[o] = 0;
      for (int k = 0; k < nps; k++) if (((sa[k] & 1) == 1) != (o == 0)) oks[o] = 0;
      ct += okt[o]; cs += oks[o];
    }
    if (ct * cs == 0) continue;
    total += ct * cs; nX++;
    if (verify) {
      int ha = ninner[0], hb = ninner[1]; (void)ha; (void)hb;
      for (int a = 0; a < nseq[0]; a++) for (int b = 0; b < nseq[1]; b++) {
        int *t = seqs[0][a], *sg = seqs[1][b];
        int ot = (t[0] & 1) ? 0 : 1, os = (sg[0] & 1) ? 0 : 1;
        if (n1 == 1) ot = 0;
        if (n2 == 1) os = 0;
        if (!okt[ot] || !oks[os]) continue;
        int pl[200] = {0}, ok = 1;
        for (int i = 0; i < n1 && ok; i++) { int p = f[t[i]]; if (!okm(pl, p, N)) ok = 0; pl[p] = 1; }
        for (int i = 0; i < n2 && ok; i++) { int p = s[sg[i]]; if (!okm(pl, p, N)) ok = 0; pl[p] = 1; }
        if (ok) vgood++; else vbad++;
      }
    }
  }
  printf("N=%d n1=%d: C_free = %.0f over %ld sets X", N, n1, total, nX);
  if (verify) printf("   [verified sequences: %ld valid, %ld INVALID]", vgood, vbad);
  printf("\n");
  return 0;
}

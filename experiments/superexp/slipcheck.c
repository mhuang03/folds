// Exhaustive check of the SLIP LEMMA (type A = evens-first), N = 2n, all D subset [1,n-1]:
//   f_i = 2i + d_i, s_i = 2i - 1 - d_{i-1}   (d_i = [i in D], d_0 = d_n = 0)
//   (a) tau valid n-sequence with  tau^{-1}(k) < tau^{-1}(q(k))  for k in D, q(k) = 2k mod* n
//       ==> (f_{tau_1},...,f_{tau_n}) valid from scratch
//   (b) sigma valid n-sequence with sigma^{-1}(p(k)) < sigma^{-1}(k+1), p(k) = 2k+1 mod* n
//       ==> (s_{sigma_1},...) valid after F = {f_i} complete.
// Also reports how many block orders are valid but NOT of this form (the lemma is only a
// sufficient condition), and type B (odds-first: S block first, then F block with the
// reversed conditions:  sigma: k+1 before p(k);  tau: q(k) before k).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int n, N; int seqs[300000][12]; int ns = 0; int cur[12];
static int valid_step(int Nn, const char *placed, int m) {
  int r = m - 1 < Nn - m ? m - 1 : Nn - m, l = 0, rr = 0;
  for (int d = 1; d <= r; d++) { l += placed[m - d]; rr += placed[m + d]; }
  return l == rr;
}
void gen(int k, char *pl) {
  if (k == n) { memcpy(seqs[ns++], cur, sizeof(cur)); return; }
  for (int m = 1; m <= n; m++) if (!pl[m] && valid_step(n, pl, m)) { pl[m] = 1; cur[k] = m; gen(k + 1, pl); pl[m] = 0; }
}
int modstar(int x) { return (x - 1) % n + 1; }
int main(int argc, char **argv) {
  int nmax = atoi(argv[1]);
  for (n = 2; n <= nmax; n++) {
    N = 2 * n; ns = 0; char pl[40] = {0}; gen(0, pl);
    long okA = 0, failA = 0, extraA = 0, okB = 0, failB = 0;
    for (int D = 0; D < (1 << (n - 1)); D++) {
      int d[40] = {0}; for (int k = 1; k < n; k++) d[k] = (D >> (k - 1)) & 1;
      int f[40], s[40]; for (int i = 1; i <= n; i++) { f[i] = 2 * i + d[i]; s[i] = 2 * i - 1 - d[i - 1]; }
      for (int t = 0; t < ns; t++) {
        int pos[40]; for (int i = 0; i < n; i++) pos[seqs[t][i]] = i;
        int cF = 1, cS = 1, cFB = 1, cSB = 1;
        for (int k = 1; k < n; k++) if (d[k]) {
          int q = modstar(2 * k), p = modstar(2 * k + 1);
          if (!(pos[k] < pos[q])) cF = 0; else cFB = 0 * 0 + cFB; // placeholder
          if (!(pos[p] < pos[k + 1])) cS = 0;
        }
        // reversed conditions for type B
        cFB = 1; cSB = 1;
        for (int k = 1; k < n; k++) if (d[k]) {
          int q = modstar(2 * k), p = modstar(2 * k + 1);
          if (!(pos[q] < pos[k])) cFB = 0;
          if (!(pos[k + 1] < pos[p])) cSB = 0;
        }
        // type A, first block F from scratch
        char P[80]; int vF = 1; memset(P, 0, sizeof(P));
        for (int i = 0; i < n; i++) { int x = f[seqs[t][i]]; if (!valid_step(N, P, x)) { vF = 0; break; } P[x] = 1; }
        // type A, second block S after F complete
        int vS = 1; memset(P, 0, sizeof(P)); for (int i = 1; i <= n; i++) P[f[i]] = 1;
        for (int i = 0; i < n; i++) { int x = s[seqs[t][i]]; if (!valid_step(N, P, x)) { vS = 0; break; } P[x] = 1; }
        if (cF) { if (vF) okA++; else failA++; } else if (vF) extraA++;
        if (cS) { if (vS) okA++; else failA++; } else if (vS) extraA++;
        // type B: S block first from scratch (needs sigma: k+1 before p(k)), F block after S
        int wS = 1; memset(P, 0, sizeof(P));
        for (int i = 0; i < n; i++) { int x = s[seqs[t][i]]; if (!valid_step(N, P, x)) { wS = 0; break; } P[x] = 1; }
        int wF = 1; memset(P, 0, sizeof(P)); for (int i = 1; i <= n; i++) P[s[i]] = 1;
        for (int i = 0; i < n; i++) { int x = f[seqs[t][i]]; if (!valid_step(N, P, x)) { wF = 0; break; } P[x] = 1; }
        if (cSB) { if (wS) okB++; else failB++; }
        if (cFB) { if (wF) okB++; else failB++; }
      }
    }
    printf("n=%d N=%d a(n)=%d: type A: %ld implications ok, %ld FAIL, %ld valid block orders outside the lemma; type B: %ld ok, %ld FAIL\n",
           n, N, ns, okA, failA, extraA, okB, failB);
  }
}

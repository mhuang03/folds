/* For N = 2n: for every pair (tau, sigma) of valid n-sequences, count the valid shuffles
   of 2tau (evens) and 2sigma-1 (odds) in the 2n-strip, W(tau, sigma).
   Prints sum W / a(n)^2, the mean of log2 W, min W, and the histogram of W.
   Usage: shuffle n [sample]   (sample > 0: random pairs) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
static int n, N;
static int *V; static long nv = 0, cap = 0;
static int cur[32]; static int used[34];
static int valid_step(int m, int *placed, int NN) {
  int r = m - 1 < NN - m ? m - 1 : NN - m, l = 0, rr = 0;
  for (int d = 1; d <= r; d++) { l += placed[m - d]; rr += placed[m + d]; }
  return l == rr;
}
static void gen(int k) {
  if (k == n) {
    if (nv == cap) { cap = cap ? 2 * cap : 1024; V = realloc(V, cap * n * sizeof(int)); }
    memcpy(V + nv * n, cur, n * sizeof(int)); nv++; return;
  }
  for (int m = 1; m <= n; m++) if (!used[m] && valid_step(m, used, n)) {
    used[m] = 1; cur[k] = m; gen(k + 1); used[m] = 0;
  }
}
/* w(m, x) in the N-strip: +1 if x in left arm of m, -1 right arm, 0 else */
static int w(int m, int x) {
  int r = m - 1 < N - m ? m - 1 : N - m;
  if (x < m && m - x <= r) return 1;
  if (x > m && x - m <= r) return -1;
  return 0;
}
static int cumE[33][66]; /* cumE[i][p] = sum_{k<i} w(p, 2tau_k)  */
static int cumO[33][66]; /* cumO[j][p] = sum_{k<j} w(p, 2sigma_k-1) */
static int mode = 0; /* 1: require every odd k to precede the even q(k) = 2k mod* N */
int main(int argc, char **argv) {
  n = atoi(argv[1]); N = 2 * n; long sample = argc > 2 ? atol(argv[2]) : 0;
  mode = argc > 3 ? atoi(argv[3]) : 0;
  memset(used, 0, sizeof used); gen(0);
  fprintf(stderr, "a(%d) = %ld\n", n, nv);
  double sumW = 0, sumlog = 0; double minW = 1e300, maxW = 0; long cnt = 0, zero = 0;
  static long hist[64];
  long total = sample ? sample : nv * nv;
  srand(12345);
  for (long it = 0; it < total; it++) {
    long ti, si;
    if (sample) { ti = ((long)rand() * 31 + rand()) % nv; si = ((long)rand() * 31 + rand()) % nv; }
    else { ti = it / nv; si = it % nv; }
    int *t = V + ti * n, *s = V + si * n;
    for (int p = 1; p <= N; p++) { cumE[0][p] = 0; cumO[0][p] = 0; }
    for (int i = 1; i <= n; i++) for (int p = 1; p <= N; p++) {
      cumE[i][p] = cumE[i-1][p] + w(p, 2 * t[i-1]);
      cumO[i][p] = cumO[i-1][p] + w(p, 2 * s[i-1] - 1);
    }
    static int need[33]; /* even step i (1-based) needs at least need[i] odds placed */
    { int pos[66]; for (int k = 0; k < n; k++) pos[2 * s[k] - 1] = k + 1;
      for (int i = 1; i <= n; i++) { need[i] = 0; if (!mode) continue;
        int e = 2 * t[i-1];
        for (int k = 1; k < N; k += 2) { int q = ((2 * k - 1) % N) + 1; if (q == e && pos[k] > need[i]) need[i] = pos[k]; } } }
    static double D[33][33];
    for (int i = 0; i <= n; i++) for (int j = 0; j <= n; j++) {
      if (!i && !j) { D[0][0] = 1; continue; }
      double v = 0;
      if (i && j >= need[i] && cumO[j][2 * t[i-1]] == 0) v += D[i-1][j];
      if (j && cumE[i][2 * s[j-1] - 1] == 0) v += D[i][j-1];
      D[i][j] = v;
    }
    double W = D[n][n];
    if (W == 0) { zero++; continue; }
    sumW += W; sumlog += log2(W); cnt++;
    if (W < minW) minW = W;
    if (W > maxW) maxW = W;
    int b = (int)floor(log2(W)); hist[b]++;
  }
  printf("zero=%ld ", zero); printf("n=%d pairs=%ld  sumW/a^2=%.4f  E log2 W=%.4f  minW=%.0f maxW=%.0f\n", n, cnt, sumW / (cnt + zero), sumlog / cnt, minW, maxW);
  for (int b = 0; b < 64; b++) if (hist[b]) printf("  [2^%d,2^%d): %ld\n", b, b + 1, hist[b]);
  return 0;
}

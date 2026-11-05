/* Exact slip sum  B(n) = sum_{D ⊆ [1,n-1]} #condF(n,D) #condS(n,D)
                       = sum_{tau, sigma in V_n} 2^{|G(tau) ∩ G'(sigma)|}
   G(tau)    = {k : tau places k before q(k) = 2k mod* n}
   G'(sigma) = {k : sigma places p(k) = (2k+1) mod* n before k+1}.
   Enumerates V_n, histograms G and G', superset sums, then the D-sum.
   Usage: bsum nmax */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n, seq[32], pos[32], used[32];
static double *hG, *hS;
static int ms(int x) { return ((x - 1) % n + n) % n + 1; }
static int valid(int m) {
  int r = m - 1 < n - m ? m - 1 : n - m, L = 0, R = 0;
  for (int d = 1; d <= r; d++) { L += used[m - d]; R += used[m + d]; }
  return L == R;
}
static void rec(int k) {
  if (k == n) {
    unsigned g = 0, s = 0;
    for (int j = 1; j <= n - 1; j++) {
      if (pos[j] < pos[ms(2 * j)]) g |= 1u << (j - 1);
      if (pos[ms(2 * j + 1)] < pos[j + 1]) s |= 1u << (j - 1);
    }
    hG[g] += 1; hS[s] += 1; return;
  }
  for (int m = 1; m <= n; m++)
    if (!used[m] && valid(m)) { used[m] = 1; pos[m] = k; rec(k + 1); used[m] = 0; }
}
int main(int argc, char **argv) {
  int nmax = atoi(argv[1]);
  for (n = 1; n <= nmax; n++) {
    size_t M = (size_t)1 << (n - 1);
    hG = calloc(M, sizeof(double)); hS = calloc(M, sizeof(double));
    memset(used, 0, sizeof used);
    rec(0);
    double a = 0; for (size_t i = 0; i < M; i++) a += hG[i];
    /* superset sums */
    for (int b = 0; b < n - 1; b++)
      for (size_t S = 0; S < M; S++)
        if (!(S >> b & 1)) { hG[S] += hG[S | ((size_t)1 << b)]; hS[S] += hS[S | ((size_t)1 << b)]; }
    double B = 0; for (size_t D = 0; D < M; D++) B += hG[D] * hS[D];
    printf("n=%d a(n)=%.0f B(n)=%.0f B/a^2=%.4f fullF=%.0f fullS=%.0f\n", n, a, B, B / (a * a),
           hG[M - 1], hS[M - 1]);
    fflush(stdout);
    free(hG); free(hS);
  }
  return 0;
}

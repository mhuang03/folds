/* classorder.c -- orders of the q residue classes mod q (N = q n, n >= 2) in which every
 * class, when it is placed as a block, sees the union of the earlier classes balanced
 * around each of its panels.  Each such order gives a(n)^q valid sequences of N = qn.
 *
 *   usage: ./classorder q [n]      (n defaults to 2; brute-force check of the class
 *                                    condition directly on the strip of length q n)
 *
 * Prints A_n(q) = number of valid class orders (subset DP over sets of residues).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int main(int argc, char **argv) {
  int q = atoi(argv[1]), n = argc > 2 ? atoi(argv[2]) : 2, N = q * n;
  /* bal[R][s] : union of residue classes R is balanced around every panel of class s */
  uint64_t NS = 1ULL << q;
  double *g = calloc(NS, sizeof(double));
  /* precompute for each panel x its window arms */
  g[0] = 1;
  for (uint64_t R = 0; R < NS - 1; R++) {
    if (g[R] == 0) continue;
    for (int s = 0; s < q; s++) {           /* residue s: panels x with x % q == s */
      if ((R >> s) & 1) continue;
      int ok = 1;
      for (int x = (s == 0 ? q : s); x <= N && ok; x += q) {
        int r = x - 1 < N - x ? x - 1 : N - x, L = 0, Rr = 0;
        for (int d = 1; d <= r; d++) { L += (R >> ((x - d) % q)) & 1; Rr += (R >> ((x + d) % q)) & 1; }
        if (L != Rr) ok = 0;
      }
      if (ok) g[R | (1ULL << s)] += g[R];
    }
  }
  printf("q=%d n=%d A=%.0f\n", q, n, g[NS - 1]);
  return 0;
}

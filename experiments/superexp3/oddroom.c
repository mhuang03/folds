/* Room in the chain recursion.  n = 2m.
   R(n) = sum_{D ⊇ odds, D ⊆ [1,n-1]} #condF(n,D) #condS(n,D)
        = sum_{tau, sigma : G(tau), G'(sigma) ⊇ odds} 2^{|G ∩ G' ∩ evens|}
   versus the parity-block part a(m)^2 B(m)  (the chain uses exactly these pairs).
   Prints R(n)/(a(m)^2 B(m)).  Usage: oddroom n */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n;
static double *c;
static int ok(unsigned S, int m, int nn) {
  int r = m - 1 < nn - m ? m - 1 : nn - m;
  unsigned L = r ? (((1u << r) - 1) << (m - 1 - r)) : 0;
  unsigned R = r ? (((1u << r) - 1) << m) : 0;
  return __builtin_popcount(S & L) == __builtin_popcount(S & R);
}
static double count(unsigned *pred, int nn) {
  size_t NS = (size_t)1 << nn; memset(c, 0, NS * sizeof(double)); c[0] = 1;
  for (size_t S = 0; S < NS; S++) if (c[S])
    for (int m = 1; m <= nn; m++) { unsigned bit = 1u << (m - 1);
      if ((S & bit) || (pred[m] & S) != pred[m] || !ok(S, m, nn)) continue; c[S | bit] += c[S]; }
  return c[NS - 1];
}
static double B(int nn, int oddonly) { /* sum over D (⊇ odds if oddonly) of condF condS */
  double tot = 0; unsigned pred[40];
  for (unsigned D = 0; D < (1u << (nn - 1)); D++) {
    int skip = 0;
    if (oddonly) for (int k = 1; k < nn; k += 2) if (!(D >> (k - 1) & 1)) skip = 1;
    if (skip) continue;
    memset(pred, 0, sizeof pred);
    for (int k = 1; k < nn; k++) if (D >> (k - 1) & 1) { int q = (2 * k - 1) % nn + 1; pred[q] |= 1u << (k - 1); }
    double F = count(pred, nn);
    memset(pred, 0, sizeof pred);
    for (int k = 1; k < nn; k++) if (D >> (k - 1) & 1) { int p = (2 * k) % nn + 1; pred[k + 1] |= 1u << (p - 1); }
    tot += F * count(pred, nn);
  }
  return tot;
}
int main(int argc, char **argv) {
  n = atoi(argv[1]); int m = n / 2;
  c = malloc(((size_t)1 << n) * sizeof(double));
  unsigned z[40]; memset(z, 0, sizeof z);
  double am = count(z, m), Bm = B(m, 0), R = B(n, 1);
  printf("n=%d  R(n)=%.0f  a(m)^2 B(m)=%.0f  ratio=%.4f\n", n, R, am * am * Bm, R / (am * am * Bm));
  return 0;
}

/* B_E(n) = sum_{E ⊆ [n]} T(E) S(E),  T(E) = #{tau in V_n : tau-conditions of E},
   S(E) = T(E^c)  (reversal).  tau-conditions (E-slip lemma, eslip.py):
     j not in E, q(j) = 2j mod* n in E      -> j before q(j)
     j in E, p(j) = (2j-1) mod* n not in E  -> j before p(j)
   Also B_D(n) = sum_{D ⊆ [1,n-1]} #condF(D) #condS(D) for comparison.
   Usage: esum n */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int n;
static int ok(unsigned S, int m) {
  int r = m - 1 < n - m ? m - 1 : n - m;
  unsigned L = r ? (((1u << r) - 1) << (m - 1 - r)) : 0;
  unsigned R = r ? (((1u << r) - 1) << m) : 0;
  return __builtin_popcount(S & L) == __builtin_popcount(S & R);
}
static int ms(int x) { return ((x - 1) % n + n) % n + 1; }
static double *c;
static double count(unsigned *pred) {
  size_t NS = (size_t)1 << n; memset(c, 0, NS * sizeof(double)); c[0] = 1;
  for (size_t S = 0; S < NS; S++) if (c[S])
    for (int m = 1; m <= n; m++) { unsigned bit = 1u << (m - 1);
      if ((S & bit) || (pred[m] & S) != pred[m] || !ok(S, m)) continue; c[S | bit] += c[S]; }
  return c[NS - 1];
}
int main(int argc, char **argv) {
  n = atoi(argv[1]);
  size_t NS = (size_t)1 << n; c = malloc(NS * sizeof(double));
  double *T = malloc(NS * sizeof(double));
  unsigned pred[40];
  for (size_t E = 0; E < NS; E++) {
    memset(pred, 0, sizeof pred);
    for (int j = 1; j <= n; j++) {
      int ej = E >> (j - 1) & 1, q = ms(2 * j), p = ms(2 * j - 1);
      if (!ej && (E >> (q - 1) & 1)) pred[q] |= 1u << (j - 1);
      if (ej && !(E >> (p - 1) & 1)) pred[p] |= 1u << (j - 1);
    }
    T[E] = count(pred);
  }
  double a = T[0], BE = 0, mx = 0;
  for (size_t E = 0; E < NS; E++) { double v = T[E] * T[(NS - 1) ^ E]; BE += v; if (v > mx) mx = v; }
  /* D-type: condF(D): k before q(k) for k in D; condS(D): p(k) = (2k+1) mod* n before k+1 */
  double BD = 0;
  size_t ND = (size_t)1 << (n > 1 ? n - 1 : 0);
  double *F = malloc(ND * sizeof(double)), *Sx = malloc(ND * sizeof(double));
  for (size_t D = 0; D < ND; D++) {
    memset(pred, 0, sizeof pred);
    for (int k = 1; k <= n - 1; k++) if (D >> (k - 1) & 1) { int q = ms(2 * k); pred[q] |= 1u << (k - 1); }
    F[D] = count(pred);
    memset(pred, 0, sizeof pred);
    for (int k = 1; k <= n - 1; k++) if (D >> (k - 1) & 1) { int p = ms(2 * k + 1); pred[k + 1] |= 1u << (p - 1); }
    Sx[D] = count(pred);
    BD += F[D] * Sx[D];
  }
  printf("n=%2d a=%.0f  B_E/a^2=%.4f  B_D/a^2=%.4f  max_E T T'/a^2=%.4f\n", n, a, BE / (a * a), BD / (a * a), mx / (a * a));
  return 0;
}

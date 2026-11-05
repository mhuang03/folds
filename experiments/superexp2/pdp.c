/* Count valid (semi-symmetric) sequences of the n-strip respecting precedence
   constraints "x before y".  Subset DP over placed sets.
   Usage: pdp n mode
   mode bit 1: F : k before q(k) = 2k mod* n          (k = 1..n-1)
   mode bit 2: F': p(k) = (2k+1) mod* n before k + 1   (k = 1..n-1)
   mode bit 4: restrict the F / F' constraints to odd k
   mode 0 gives a(n).  Prints the exact count. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 u128;
static int n;
static unsigned pred[40];
static void pr(u128 x) {
  char b[64]; int i = 63; b[i] = 0;
  if (!x) { printf("0"); return; }
  while (x) { b[--i] = '0' + (int)(x % 10); x /= 10; }
  printf("%s", b + i);
}
static int ms(int x) { return ((x - 1) % n + n) % n + 1; }
int main(int argc, char **argv) {
  n = atoi(argv[1]); int mode = atoi(argv[2]);
  memset(pred, 0, sizeof pred);
  for (int k = 1; k <= n - 1; k++) {
    if ((mode & 4) && k % 2 == 0) continue;
    if (mode & 1) { int q = ms(2 * k); pred[q] |= 1u << (k - 1); }
    if (mode & 2) { int p = ms(2 * k + 1); pred[k + 1] |= 1u << (p - 1); }
  }
  size_t N = (size_t)1 << n;
  u128 *c = calloc(N, sizeof(u128)); c[0] = 1;
  for (size_t S = 0; S < N; S++) {
    if (!c[S]) continue;
    for (int m = 1; m <= n; m++) {
      unsigned b = 1u << (m - 1);
      if (S & b) continue;
      if ((pred[m] & S) != pred[m]) continue;
      int r = m - 1 < n - m ? m - 1 : n - m;
      unsigned L = r ? (((1u << r) - 1) << (m - 1 - r)) : 0;
      unsigned R = r ? (((1u << r) - 1) << m) : 0;
      if (__builtin_popcount(S & L) != __builtin_popcount(S & R)) continue;
      c[S | b] += c[S];
    }
  }
  pr(c[N - 1]); printf("\n");
  return 0;
}

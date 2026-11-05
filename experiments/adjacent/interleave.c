/* interleave.c NMAX: for J(N, k) (order [1, k] in the N-strip), test the ansatz
   "tops k, k-1, ..., h+1 (descending) alternating with the smalls [1, h] in some order,
   starting with a top" for h = floor(k/2) (k - h = h or h + 1 tops).  Subset DP over the
   smalls.  Prints the (N, k) where the ansatz fails. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int N, k, h;
static uint32_t L[64], R[64];
static int valid(uint64_t S, int m) {
  return __builtin_popcountll(S & L[m]) == __builtin_popcountll(S & R[m]);
}
int main(int argc, char **argv) {
  int NMAX = atoi(argv[1]);
  for (N = 2; N <= NMAX; N++) {
    for (int m = 1; m <= N; m++) {
      int r = m - 1 < N - m ? m - 1 : N - m;
      L[m] = R[m] = 0;
      for (int d = 1; d <= r; d++) { L[m] |= 1u << (m - d - 1); R[m] |= 1u << (m + d - 1); }
    }
    printf("N=%d fail k:", N);
    for (k = 1; k <= N; k++) {
      h = k / 2;
      int nt = k - h;
      uint8_t *B = calloc((size_t)1 << h, 1); /* B[s] = completable from smalls s */
      uint32_t fullS = (1u << h) - 1;
      /* state: smalls s placed, j = |s|; tops placed: before small j+1 there are j+1 tops;
         the full sequence: t1 s1 t2 s2 ... ; tops k..k-i+1 = bits */
      for (uint32_t s = fullS;; s--) {
        int j = __builtin_popcount(s);
        uint32_t tops = 0;
        for (int i = 0; i < j; i++) tops |= 1u << (k - i - 1); /* tops placed: j */
        /* next: top j+1 (if j < nt), then small j+1 */
        int ok = 1;
        uint32_t S = s | tops;
        if (j < nt) {
          int t = k - j;
          if (!valid(S, t)) ok = 0;
          S |= 1u << (t - 1);
        }
        if (!ok) B[s] = 0;
        else if (s == fullS) B[s] = 1; /* all smalls placed: remaining tops checked above */
        else {
          /* remaining tops after all smalls: if nt > h + 1 we need more, but nt <= h + 1 */
          B[s] = 0;
          for (int y = 1; y <= h; y++)
            if (!(s >> (y - 1) & 1) && valid(S, y) && B[s | 1u << (y - 1)]) { B[s] = 1; break; }
        }
        if (s == 0) break;
      }
      if (!B[0]) printf(" %d", k);
      free(B);
    }
    printf("\n");
  }
  return 0;
}

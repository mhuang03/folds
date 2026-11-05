/* rsparity.c k1 k2: rotation-stable sequences of the k-strip (live2/PROOFS 3) restricted to
   parity chains: the parity class of the start first (complete), then the other class.
   Prints the (nu, t) with no such sequence. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int k, rot[64];
static uint64_t L[64], R[64];
static int ok(uint64_t S, int t) {
  if (__builtin_popcountll(S & L[t]) != __builtin_popcountll(S & R[t])) return 0;
  uint64_t Sr = 0;
  for (int x = 1; x <= k; x++) if (S >> (x - 1) & 1) Sr |= 1ull << (rot[x] - 1);
  int u = rot[t];
  return __builtin_popcountll(Sr & L[u]) == __builtin_popcountll(Sr & R[u]);
}
int main(int argc, char **argv) {
  int k1 = atoi(argv[1]), k2 = atoi(argv[2]);
  for (k = k1; k <= k2; k++) {
    for (int m = 1; m <= k; m++) {
      int r = m - 1 < k - m ? m - 1 : k - m;
      L[m] = R[m] = 0;
      for (int d = 1; d <= r; d++) { L[m] |= 1ull << (m - d - 1); R[m] |= 1ull << (m + d - 1); }
    }
    printf("%d:", k); fflush(stdout);
    for (int nu = 0; nu < k; nu++) {
      for (int t = 1; t <= k; t++) rot[t] = (t - 1 + nu) % k + 1;
      for (int c = 0; c < 2; c++) {          /* first class: parity c (1 = odd) */
        int A[64], na = 0, B[64], nb = 0;
        for (int x = 1; x <= k; x++) { if ((x & 1) == c) A[na++] = x; else B[nb++] = x; }
        uint64_t fullA = 0; for (int i = 0; i < na; i++) fullA |= 1ull << (A[i] - 1);
        uint8_t *d2 = malloc(1u << nb), *d1 = malloc(1u << na);
        for (int64_t s = (1ll << nb) - 1; s >= 0; s--) {
          if (s == (1ll << nb) - 1) { d2[s] = 1; continue; }
          uint64_t S = fullA; for (int i = 0; i < nb; i++) if (s >> i & 1) S |= 1ull << (B[i] - 1);
          uint8_t r = 0;
          for (int i = 0; i < nb && !r; i++) if (!(s >> i & 1) && ok(S, B[i]) && d2[s | (1 << i)]) r = 1;
          d2[s] = r;
        }
        for (int64_t s = (1ll << na) - 1; s >= 0; s--) {
          if (s == (1ll << na) - 1) { d1[s] = d2[0]; continue; }
          uint64_t S = 0; for (int i = 0; i < na; i++) if (s >> i & 1) S |= 1ull << (A[i] - 1);
          uint8_t r = 0;
          for (int i = 0; i < na && !r; i++) if (!(s >> i & 1) && ok(S, A[i]) && d1[s | (1 << i)]) r = 1;
          d1[s] = r;
        }
        for (int i = 0; i < na; i++) if (!d1[1u << i]) printf(" (%d,%d)", nu, A[i]);
        free(d1); free(d2);
      }
    }
    printf("\n"); fflush(stdout);
  }
}

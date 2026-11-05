/* Count semi-symmetric fold sequences of [1..N] with the constraints of some panels removed.
   usage: dpx N [p1 p2 ...]   (panels p_i are unconstrained)   -> prints the count.
   Subset DP over sets S (2^N uint64). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
  int N = atoi(argv[1]);
  int con[64]; uint64_t L[64], R[64];
  for (int m = 1; m <= N; m++) {
    int D = m - 1 < N - m ? m - 1 : N - m; con[m] = D > 0; L[m] = R[m] = 0;
    for (int d = 1; d <= D; d++) { L[m] |= 1ULL << (m - d - 1); R[m] |= 1ULL << (m + d - 1); }
  }
  for (int i = 2; i < argc; i++) con[atoi(argv[i])] = 0;
  uint64_t full = (1ULL << N) - 1;
  uint64_t *g = calloc(1ULL << N, 8);
  g[0] = 1;
  for (uint64_t S = 0; S < full; S++) {
    uint64_t c = g[S]; if (!c) continue;
    for (int m = 1; m <= N; m++) {
      uint64_t b = 1ULL << (m - 1); if (S & b) continue;
      if (con[m] && __builtin_popcountll(S & L[m]) != __builtin_popcountll(S & R[m])) continue;
      g[S | b] += c;
    }
  }
  printf("%llu\n", (unsigned long long)g[full]);
  return 0;
}

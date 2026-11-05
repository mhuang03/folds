/* oddmax.c -- max over ALL sets S of |S| = k of the number of valid next panels V(S).
 *
 *   usage: ./oddmax N
 *
 * Tests the parity lemma: |S| odd  =>  V(S) <= ceil(N/2)   (PROOFS.txt 2.2).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int main(int argc, char **argv) {
  int N = atoi(argv[1]);
  uint64_t Lm[64], Rm[64];
  for (int m = 1; m <= N; m++) {
    int D = m - 1 < N - m ? m - 1 : N - m;
    Lm[m] = Rm[m] = 0;
    for (int d = 1; d <= D; d++) { Lm[m] |= 1ULL << (m - d - 1); Rm[m] |= 1ULL << (m + d - 1); }
  }
  int mx[64] = {0};
  for (uint64_t S = 0; S < (1ULL << N); S++) {
    int v = 0;
    for (int m = 1; m <= N; m++) {
      if ((S >> (m - 1)) & 1) continue;
      if (__builtin_popcountll(S & Lm[m]) == __builtin_popcountll(S & Rm[m])) v++;
    }
    int k = __builtin_popcountll(S);
    if (v > mx[k]) mx[k] = v;
  }
  printf("N=%d ceil(N/2)=%d  max V by k:", N, (N + 1) / 2);
  for (int k = 0; k < N; k++) printf(" %d:%d", k, mx[k]);
  printf("\n");
  return 0;
}

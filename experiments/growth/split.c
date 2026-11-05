/* split.c -- how do valid sequences of N decompose into their even / odd subsequences?
 *
 *   usage: ./split N
 *
 * Enumerates all valid sequences of length N (DFS), and for each one checks whether the
 * even subsequence (halved) and the odd subsequence (as (x+1)/2) are valid sequences of
 * the half problems.  Also histograms the number of parity changes.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static int N;
static uint64_t Lm[64], Rm[64];
static uint64_t LmE[64], RmE[64], LmO[64], RmO[64];
static int nE, nO;
static int seq[64];
static long long total, both, evok, odok, hist[64];

static int valid(uint64_t S, int m, uint64_t *L, uint64_t *R) {
  return __builtin_popcountll(S & L[m]) == __builtin_popcountll(S & R[m]);
}
static void mk(int n, uint64_t *L, uint64_t *R) {
  for (int m = 1; m <= n; m++) {
    int D = m - 1 < n - m ? m - 1 : n - m;
    L[m] = R[m] = 0;
    for (int d = 1; d <= D; d++) { L[m] |= 1ULL << (m - d - 1); R[m] |= 1ULL << (m + d - 1); }
  }
}
static void check(void) {
  total++;
  uint64_t SE = 0, SO = 0; int ve = 1, vo = 1, ch = 0;
  for (int k = 0; k < N; k++) {
    int m = seq[k];
    if (k && (seq[k] & 1) != (seq[k - 1] & 1)) ch++;
    if (m % 2 == 0) { int j = m / 2; if (ve && !valid(SE, j, LmE, RmE)) ve = 0; SE |= 1ULL << (j - 1); }
    else { int j = (m + 1) / 2; if (vo && !valid(SO, j, LmO, RmO)) vo = 0; SO |= 1ULL << (j - 1); }
  }
  evok += ve; odok += vo; both += ve && vo; hist[ch]++;
}
static void dfs(int k, uint64_t S) {
  if (k == N) { check(); return; }
  for (int m = 1; m <= N; m++) {
    uint64_t b = 1ULL << (m - 1);
    if (S & b) continue;
    if (!valid(S, m, Lm, Rm)) continue;
    seq[k] = m; dfs(k + 1, S | b);
  }
}
int main(int argc, char **argv) {
  N = atoi(argv[1]);
  nE = N / 2; nO = (N + 1) / 2;
  mk(N, Lm, Rm); mk(nE, LmE, RmE); mk(nO, LmO, RmO);
  dfs(0, 0);
  printf("N=%d total=%lld evenhalf_ok=%lld oddhalf_ok=%lld both=%lld\n", N, total, evok, odok, both);
  printf("parity changes histogram:");
  for (int i = 0; i < N; i++) if (hist[i]) printf(" %d:%lld", i, hist[i]);
  printf("\n");
  return 0;
}

/* blocktest.c N: for every reachable 2-set {u,v} (u<v) test whether the complement
   C = [N] \ {u,v} has a valid ordering from scratch of block form
     mode 0: evens of C first, then odds of C;   mode 1: odds of C first, then evens.
   Prints the pairs (live ones only) that have neither block form. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int N;
static uint32_t L[40], Rm[40];
static int valid(uint32_t S, int m) {
  return __builtin_popcount(S & L[m]) == __builtin_popcount(S & Rm[m]);
}
static uint8_t *reach;
#define GET(s) ((reach[(s) >> 3] >> ((s) & 7)) & 1)
#define SET(s) (reach[(s) >> 3] |= 1 << ((s) & 7))
/* reachability restricted: from 0, add only elements of A until A done, then elements of B. */
static uint8_t *memo; /* 0 unknown 1 yes 2 no ; indexed by set within A|B */
static uint32_t gA, gB;
static int dfs(uint32_t S) {
  if (S == (gA | gB)) return 1;
  if (memo[S]) return memo[S] == 1;
  int ok = 0;
  uint32_t pool = ((S & gA) == gA) ? (gB & ~S) : (gA & ~S);
  for (int m = 1; m <= N && !ok; m++)
    if ((pool >> (m - 1) & 1) && valid(S, m)) ok = dfs(S | 1u << (m - 1));
  memo[S] = ok ? 1 : 2;
  return ok;
}
int main(int argc, char **argv) {
  N = atoi(argv[1]);
  for (int m = 1; m <= N; m++) {
    int r = m - 1 < N - m ? m - 1 : N - m;
    L[m] = Rm[m] = 0;
    for (int d = 1; d <= r; d++) { L[m] |= 1u << (m - d - 1); Rm[m] |= 1u << (m + d - 1); }
  }
  uint64_t full = (1ull << N) - 1;
  reach = calloc((full >> 3) + 1, 1);
  memo = malloc(full + 1);
  SET(0);
  for (uint64_t S = 0; S <= full; S++) {
    if (!GET(S)) continue;
    for (int m = 1; m <= N; m++)
      if (!(S >> (m - 1) & 1) && valid((uint32_t)S, m)) SET(S | (1ull << (m - 1)));
  }
  uint32_t ev = 0, od = 0;
  for (int m = 1; m <= N; m++) { if (m % 2) od |= 1u << (m - 1); else ev |= 1u << (m - 1); }
  int bad = 0;
  for (int u = 1; u <= N; u++)
    for (int v = u + 1; v <= N; v++) {
      uint32_t P = 1u << (u - 1) | 1u << (v - 1);
      if (!valid(1u << (u - 1), v) && !valid(1u << (v - 1), u)) continue;
      uint32_t C = (uint32_t)full & ~P;
      if (!GET(C)) continue;
      int res[2];
      for (int mode = 0; mode < 2; mode++) {
        gA = C & (mode ? od : ev); gB = C & (mode ? ev : od);
        memset(memo, 0, full + 1);
        res[mode] = dfs(0);
      }
      if (!res[0] && !res[1]) { bad++; printf("noblock %d %d %d\n", N, u, v); }
      else printf("block %d %d %d %d%d\n", N, u, v, res[0], res[1]);
    }
  printf("summary N=%d bad=%d\n", N, bad);
  return 0;
}

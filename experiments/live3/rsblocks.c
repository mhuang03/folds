/* rsblocks.c k1 k2: rotation-stable sequences of the k-strip (live2/PROOFS 3) that are block
   chains mod j: the classes {x = a mod j} of [1, k] placed as complete blocks, for some
   2 <= j < k.  For each (nu, t) prints the list of j that work; '-' marks (nu, t) with none.
   Memoised DFS over (done blocks, current block, subset of the current block). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int k, j, rot[64], cls[64];
static uint64_t L[64], R[64], blk[64];
static int ok(uint64_t S, int t) {
  if (__builtin_popcountll(S & L[t]) != __builtin_popcountll(S & R[t])) return 0;
  uint64_t Sr = 0;
  for (int x = 1; x <= k; x++) if (S >> (x - 1) & 1) Sr |= 1ull << (rot[x] - 1);
  int u = rot[t];
  return __builtin_popcountll(Sr & L[u]) == __builtin_popcountll(Sr & R[u]);
}
/* memo keyed by placed set S (it determines done blocks and current block's subset) */
#define HB 22
static uint64_t hkey[1 << HB]; static int8_t hval[1 << HB];
static int lookup(uint64_t S, int *v) {
  uint64_t h = (S * 0x9E3779B97F4A7C15ull) >> (64 - HB);
  while (hval[h] != -1) { if (hkey[h] == S) { *v = hval[h]; return 1; } h = (h + 1) & ((1 << HB) - 1); }
  return 0;
}
static void store(uint64_t S, int v) {
  uint64_t h = (S * 0x9E3779B97F4A7C15ull) >> (64 - HB);
  while (hval[h] != -1) h = (h + 1) & ((1 << HB) - 1);
  hkey[h] = S; hval[h] = v;
}
static uint64_t full;
static int dfs(uint64_t S) {
  if (S == full) return 1;
  int v; if (lookup(S, &v)) return v;
  /* current block: a block partially placed, else any block not started */
  int cur = -1;
  for (int a = 0; a < j; a++) { uint64_t p = S & blk[a]; if (p && p != blk[a]) cur = a; }
  int res = 0;
  for (int x = 1; x <= k && !res; x++) {
    if (S >> (x - 1) & 1) continue;
    if (cur >= 0 && cls[x] != cur) continue;
    if (ok(S, x) && dfs(S | (1ull << (x - 1)))) res = 1;
  }
  store(S, res);
  return res;
}
int main(int argc, char **argv) {
  int k1 = atoi(argv[1]), k2 = atoi(argv[2]);
  for (k = k1; k <= k2; k++) {
    for (int m = 1; m <= k; m++) {
      int r = m - 1 < k - m ? m - 1 : k - m;
      L[m] = R[m] = 0;
      for (int d = 1; d <= r; d++) { L[m] |= 1ull << (m - d - 1); R[m] |= 1ull << (m + d - 1); }
    }
    full = (k == 64) ? ~0ull : ((1ull << k) - 1);
    printf("q=%d\n", k);
    for (int nu = 1; nu < k; nu++) {
      for (int t = 1; t <= k; t++) rot[t] = (t - 1 + nu) % k + 1;
      char line[4096]; int pos = 0; pos += sprintf(line + pos, " nu=%d:", nu);
      static int works[64][64]; memset(works, 0, sizeof works);
      for (j = 2; j < k; j++) {
        for (int a = 0; a < j; a++) blk[a] = 0;
        for (int x = 1; x <= k; x++) { cls[x] = x % j; blk[x % j] |= 1ull << (x - 1); }
        memset(hval, -1, sizeof hval);
        for (int t = 1; t <= k; t++) works[t][j] = dfs(1ull << (t - 1));
      }
      for (int t = 1; t <= k; t++) {
        pos += sprintf(line + pos, " %d[", t);
        int any = 0;
        for (j = 2; j < k; j++) if (works[t][j]) { pos += sprintf(line + pos, any ? ",%d" : "%d", j); any = 1; }
        pos += sprintf(line + pos, any ? "]" : "-]");
      }
      printf("%s\n", line); fflush(stdout);
    }
  }
}

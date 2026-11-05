/* copyfirst.c N copiesfile: for each adjacent pair D = {r, r+1}, list the window copies X
   (from live2/copies.c output: "mask size flag") with X n D empty such that
   [N] \ D is reachable as "X first (any valid order of its strip), then Y = [N] \ X \ D".
   Second phase: Y on the background X, equivalently (reversed) Y on the background D. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int N;
static uint32_t L[40], R[40];
static int valid(uint32_t S, int m) {
  return __builtin_popcount(S & L[m]) == __builtin_popcount(S & R[m]);
}
static uint8_t *B;
static int phase2(uint32_t bg, uint32_t Y) {
  /* order Y on background bg; DP over subsets of Y */
  int idx[32], n = 0;
  for (int i = 0; i < N; i++) if (Y >> i & 1) idx[n++] = i + 1;
  uint32_t full = (1u << n) - 1;
  memset(B, 0, (size_t)1 << n);
  B[full] = 1;
  for (uint32_t s = full;; s--) {
    if (s != full) {
      uint32_t S = bg;
      for (int i = 0; i < n; i++) if (s >> i & 1) S |= 1u << (idx[i] - 1);
      for (int i = 0; i < n; i++)
        if (!(s >> i & 1) && B[s | 1u << i] && valid(S, idx[i])) { B[s] = 1; break; }
    }
    if (s == 0) break;
  }
  return B[0];
}
int main(int argc, char **argv) {
  N = atoi(argv[1]);
  for (int m = 1; m <= N; m++) {
    int r = m - 1 < N - m ? m - 1 : N - m;
    L[m] = R[m] = 0;
    for (int d = 1; d <= r; d++) { L[m] |= 1u << (m - d - 1); R[m] |= 1u << (m + d - 1); }
  }
  B = malloc((size_t)1 << N);
  uint32_t copies[4096]; int nc = 0;
  FILE *f = fopen(argv[2], "r");
  unsigned mask; int p, g;
  while (fscanf(f, "%u %d %d", &mask, &p, &g) == 3) copies[nc++] = mask;
  fclose(f);
  uint32_t full = (1u << N) - 1;
  for (int r = 1; r < N; r++) {
    uint32_t D = 3u << (r - 1);
    int cnt = 0, best = 0; uint32_t bestX = 0;
    for (int c = 0; c < nc; c++) {
      uint32_t X = copies[c];
      if (X & D) continue;
      int sz = __builtin_popcount(X);
      if (sz < 2 || sz == N) continue;
      if (phase2(D, full & ~X & ~D)) {
        cnt++;
        if (sz > best) { best = sz; bestX = X; }
      }
    }
    printf("r=%d: %d copies work; largest:", r, cnt);
    for (int i = 0; i < N; i++) if (bestX >> i & 1) printf(" %d", i + 1);
    printf("\n");
  }
  return 0;
}

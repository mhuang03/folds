/* chain.c: does a target set T of the N-strip (on a background) have a valid ordering in
   which the panels of a chain C appear in a prescribed order (others free)?
   DP over (subset of free panels, chain position).
   Modes:
     chain j N k h      J(N, k): T = [1, k], chain = k, k-1, ..., h+1 (descending)
     chain q N n h      P2 mirrored: T = [1, n-2], background {n-1, n}, chain = h+1, ..., n-2 asc.
     chain Q N n h      as q, but background = [n+1, N] (the forward form of Q)
     chain p / P        as q / Q with the chain descending (n-2, ..., h+1)
   With h = -1: try all h and print the set of h that work. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
static int N;
static uint64_t L[64], R[64];
static int valid(uint64_t S, int m) {
  return __builtin_popcountll(S & L[m]) == __builtin_popcountll(S & R[m]);
}
static int freeP[64], nf, chainP[64], nc;
static int dualN = 0; /* if > 0: free steps must also be valid in the dualN-strip, counting free panels only */
static uint64_t L2[64], R2[64];
static int valid2(uint64_t Sfree, int m) {
  if (!dualN) return 1;
  return __builtin_popcountll(Sfree & L2[m]) == __builtin_popcountll(Sfree & R2[m]);
}
static uint64_t bg;
/* PARITY=1: all odd free panels before the even ones; PARITY=2: evens first */
static int parmode = 0;
static int parok(uint32_t s, int i) {
  if (!parmode) return 1;
  int firstpar = parmode == 1 ? 1 : 0; /* parity (y & 1) of the block placed first */
  if ((freeP[i] & 1) == firstpar) return 1;
  for (int j = 0; j < nf; j++)
    if ((freeP[j] & 1) == firstpar && !(s >> j & 1)) return 0;
  return 1;
}
static int solve(void) {
  size_t states = ((size_t)1 << nf) * (nc + 1);
  uint8_t *B = calloc(states, 1);
  uint32_t fullF = (uint32_t)((1ull << nf) - 1);
  /* index = s * (nc+1) + c */
  for (int64_t s = fullF; s >= 0; s--)
    for (int c = nc; c >= 0; c--) {
      size_t id = (size_t)s * (nc + 1) + c;
      if (s == fullF && c == nc) { B[id] = 1; continue; }
      uint64_t S = bg;
      for (int i = 0; i < nf; i++) if (s >> i & 1) S |= 1ull << (freeP[i] - 1);
      for (int i = 0; i < c; i++) S |= 1ull << (chainP[i] - 1);
      int ok = 0;
      if (c < nc && valid(S, chainP[c]) && B[(size_t)s * (nc + 1) + c + 1]) ok = 1;
      uint64_t Sf = 0;
      for (int i = 0; i < nf; i++) if (s >> i & 1) Sf |= 1ull << (freeP[i] - 1);
      for (int i = 0; !ok && i < nf; i++)
        if (!(s >> i & 1) && parok(s, i) && valid(S, freeP[i]) && valid2(Sf, freeP[i]) && B[(size_t)(s | 1u << i) * (nc + 1) + c]) ok = 1;
      B[id] = ok;
    }
  int r = B[0];
  if (r && getenv("SHOW")) {
    /* greedy reconstruction: prefer the chain step, then the smallest free panel */
    uint32_t s = 0;
    int c = 0;
    printf("\n    ");
    while (!(s == fullF && c == nc)) {
      uint64_t S = bg;
      for (int i = 0; i < nf; i++) if (s >> i & 1) S |= 1ull << (freeP[i] - 1);
      for (int i = 0; i < c; i++) S |= 1ull << (chainP[i] - 1);
      if (c < nc && valid(S, chainP[c]) && B[(size_t)s * (nc + 1) + c + 1]) {
        printf(" [%d]", chainP[c]); c++; continue;
      }
      int pref = getenv("SHOW")[0] == 't';
      for (int ii = 0; ii < nf; ii++) {
        int i = pref ? nf - 1 - ii : ii;
        if (!(s >> i & 1) && valid(S, freeP[i]) && B[(size_t)(s | 1u << i) * (nc + 1) + c]) {
          printf(" %d", freeP[i]); s |= 1u << i; break;
        }
      }
    }
  }
  free(B);
  return r;
}
int main(int argc, char **argv) {
  char mode = argv[1][0];
  N = atoi(argv[2]);
  int a = atoi(argv[3]);
  int h0 = atoi(argv[4]);
  for (int m = 1; m <= N; m++) {
    int r = m - 1 < N - m ? m - 1 : N - m;
    L[m] = R[m] = 0;
    for (int d = 1; d <= r; d++) { L[m] |= 1ull << (m - d - 1); R[m] |= 1ull << (m + d - 1); }
  }
  if (getenv("PARITY")) parmode = atoi(getenv("PARITY"));
  if (getenv("DUAL")) {
    dualN = atoi(getenv("DUAL"));
    if (dualN < 0) dualN = N + dualN; /* relative */
    for (int m = 1; m <= dualN; m++) {
      int r = m - 1 < dualN - m ? m - 1 : dualN - m;
      L2[m] = R2[m] = 0;
      for (int d = 1; d <= r; d++) { L2[m] |= 1ull << (m - d - 1); R2[m] |= 1ull << (m + d - 1); }
    }
  }
  int top = mode == 'j' ? a : a - 2;
  int hlo = h0 < 0 ? 0 : h0, hhi = h0 < 0 ? top : h0;
  printf("%c N=%d a=%d works for h:", mode, N, a);
  for (int h = hlo; h <= hhi; h++) {
    if (h > 26 || top - h > 40) continue;
    nf = 0; nc = 0; bg = 0;
    for (int y = 1; y <= h; y++) freeP[nf++] = y;
    if (mode == 'j') for (int y = a; y > h; y--) chainP[nc++] = y;
    else if (mode == 'q' || mode == 'Q') for (int y = h + 1; y <= a - 2; y++) chainP[nc++] = y;
    else for (int y = a - 2; y > h; y--) chainP[nc++] = y;
    if (mode == 'q' || mode == 'p') bg = 3ull << (a - 2);
    if (mode == 'Q' || mode == 'P') for (int y = a + 1; y <= N; y++) bg |= 1ull << (y - 1);
    if (solve()) printf(" %d", h);
  }
  printf("\n");
  return 0;
}

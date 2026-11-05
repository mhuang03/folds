// bg.c N [kMODE] D1 D2 ... [z Z1 Z2 ...] (Z = absent panels, never placed) : background-picture exact solver for co-reachability of D in [N].
// Prints one ordering of [N]\D on background D (each step balanced w.r.t. D + earlier),
// choosing at every step the valid completable panel with the smallest key:
// mode 0 = distance to the middle, 1 = smallest, 2 = largest.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
int N, t, T[64], pos[64];
uint64_t Lm[64], Rm[64];
uint8_t *good;
int Dset[64], Zset[64];
int main(int argc, char **argv) {
  N = atoi(argv[1]);
  memset(Dset, 0, sizeof Dset);
  int mode = 0, k = 2;
  if (argv[2][0] == 'k') { mode = atoi(argv[2] + 1); k = 3; }
  memset(Zset, 0, sizeof Zset);
  int z = 0;
  for (int i = k; i < argc; i++) { if (argv[i][0] == 'z') { z = 1; continue; }
    if (z) Zset[atoi(argv[i])] = 1; else Dset[atoi(argv[i])] = 1; }
  t = 0;
  for (int x = 1; x <= N; x++) { pos[x] = -1; if (!Dset[x] && !Zset[x]) { pos[x] = t; T[t++] = x; } }
  int dimb[64];
  for (int i = 0; i < t; i++) {
    int m = T[i], r = (m - 1 < N - m) ? m - 1 : N - m, d = 0;
    Lm[i] = Rm[i] = 0;
    for (int j = 0; j < t; j++) {
      int x = T[j];
      if (x >= m - r && x < m) Lm[i] |= 1ull << j;
      if (x > m && x <= m + r) Rm[i] |= 1ull << j;
    }
    for (int x = 1; x <= N; x++) if (Dset[x]) {
      if (x >= m - r && x < m) d++; else if (x > m && x <= m + r) d--;
    }
    dimb[i] = d;
  }
  uint64_t full = (1ull << t) - 1;
  good = malloc(1ull << t);
  for (int64_t S = full; S >= 0; S--) {
    if ((uint64_t)S == full) { good[S] = 1; continue; }
    int g = 0;
    for (int i = 0; i < t && !g; i++) if (!(S >> i & 1)) {
      int I = dimb[i] + __builtin_popcountll(S & Lm[i]) - __builtin_popcountll(S & Rm[i]);
      if (I == 0 && good[S | (1ull << i)]) g = 1;
    }
    good[S] = g;
  }
  if (!good[0]) { printf("N=%d not co-reachable\n", N); return 0; }
  uint64_t S = 0;
  printf("N=%d order:", N);
  while (S != full) {
    int best = -1; double bk = 1e9;
    for (int i = 0; i < t; i++) if (!(S >> i & 1)) {
      int I = dimb[i] + __builtin_popcountll(S & Lm[i]) - __builtin_popcountll(S & Rm[i]);
      if (I == 0 && good[S | (1ull << i)]) {
        int m = T[i]; double key;
        if (mode == 0) key = abs(2 * m - (N + 1)); else if (mode == 1) key = m; else key = -m;
        if (key < bk) { bk = key; best = i; }
      }
    }
    printf(" %d", T[best]);
    S |= 1ull << best;
  }
  printf("\n");
  return 0;
}

/* copyinfo.c: which sets X have g(X) = a(|X|), and which copies have g(X^c) = a(N-|X|).
   usage: copyinfo N   (needs a(1..N) from ../semi_counts.txt)
   For 2 <= |X| <= N-2 prints, per size k: #copies, #non-copies with g(X) = a(k) (and g > 0),
   #copies with g(X^c) = a(N-k), #neutral, and min/max of g(X^c)/a(N-k) over copies. */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
  int N = atoi(argv[1]);
  uint64_t A[64] = {0};
  FILE *f = fopen("../semi_counts.txt", "r"); char line[256];
  while (fgets(line, sizeof line, f)) { if (line[0] == '#') continue; int n; unsigned long long v;
    if (sscanf(line, "%d %llu", &n, &v) == 2 && n < 64) A[n] = v; }
  fclose(f);
  uint64_t full = (1ULL << N) - 1, M = 1ULL << N, L[64], R[64];
  for (int m = 1; m <= N; m++) { int D = m - 1 < N - m ? m - 1 : N - m; L[m] = R[m] = 0;
    for (int d = 1; d <= D; d++) { L[m] |= 1ULL << (m - d - 1); R[m] |= 1ULL << (m + d - 1); } }
  uint64_t *g = calloc(M, 8), *h = calloc(M, 8);
  g[0] = 1;
  for (uint64_t S = 0; S < full; S++) { if (!g[S]) continue;
    for (int m = 1; m <= N; m++) { uint64_t b = 1ULL << (m - 1); if (S & b) continue;
      if (__builtin_popcountll(S & L[m]) == __builtin_popcountll(S & R[m])) g[S | b] += g[S]; } }
  h[full] = 1;
  for (uint64_t S = full; S-- > 0;) { uint64_t s = 0;
    for (int m = 1; m <= N; m++) { uint64_t b = 1ULL << (m - 1); if (S & b) continue;
      if (__builtin_popcountll(S & L[m]) == __builtin_popcountll(S & R[m])) s += h[S | b]; }
    h[S] = s; }
  { double worst = 0; long viol = 0;  /* is g(X) <= a(|X|) for every X?  max over non-copies */
    for (uint64_t S = 1; S < full; S++) { int k = __builtin_popcountll(S), cp = 1;
      for (int m = 1; m <= N && cp; m++) if ((S >> (m - 1) & 1) && __builtin_popcountll(S & L[m]) != __builtin_popcountll(S & R[m])) cp = 0;
      if (g[S] > A[k]) viol++;
      if (!cp) { double r = (double)g[S] / A[k]; if (r > worst) worst = r; } }
    printf("N=%d  #X with g(X) > a(|X|): %ld;  max g(X)/a(|X|) over non-copies: %.4f\n", N, viol, worst); }
  printf("N=%d  k #copies #noncopy(g=a(k)) #copies(h=a(N-k)) #neutral  min,max h/a(N-k) over copies\n", N);
  for (int k = 2; k <= N - 2; k++) {
    long nc = 0, ng = 0, nh = 0, nn = 0; double mn = 1e300, mx = 0;
    for (uint64_t S = 1; S < full; S++) { if (__builtin_popcountll(S) != k) continue;
      int cp = 1, nt = 1;
      for (int m = 1; m <= N; m++) { int b = __builtin_popcountll(S & L[m]) == __builtin_popcountll(S & R[m]);
        if (!b) { nt = 0; if (S >> (m - 1) & 1) cp = 0; } }
      if (cp) { nc++; if (h[S] == A[N - k]) nh++; double r = (double)h[S] / A[N - k]; if (r < mn) mn = r; if (r > mx) mx = r; }
      else if (g[S] == A[k]) ng++;
      if (nt) nn++; }
    printf("  %d %ld %ld %ld %ld  %.4f %.4f\n", k, nc, ng, nh, nn, nc ? mn : 0, mx);
  }
  return 0;
}

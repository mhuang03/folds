/* fixeds.c -- exhaustive max V(S) over all S of a FIXED size s (s <= 6), for one N.
   Validity of a free m: I(m) = Ptilde(2m-1) - 2 P(m-1) = 0 (cyclic form, Folds/Upper.lean).
   usage: ./fixeds N s      prints N s maxV floor(2N/3) and one maximiser */
#include <stdio.h>
#include <stdlib.h>
int N, s, best = -1, bestS[16], in[512], P[512];
int cnt(void) {
  /* P[j] = #S in [1, j] for 0 <= j <= N */
  P[0] = 0; for (int j = 1; j <= N; j++) P[j] = P[j - 1] + in[j];
  int V = 0;
  for (int m = 1; m <= N; m++) { if (in[m]) continue;
    int j = 2 * m - 1; int pt = P[j % N] + (j / N) * s;
    if (pt == 2 * P[m - 1]) V++; }
  return V; }
int cur[16];
void rec(int i, int lo) {
  if (i == s) { int V = cnt(); if (V > best) { best = V; for (int k = 0; k < s; k++) bestS[k] = cur[k]; } return; }
  for (int x = lo; x <= N; x++) { cur[i] = x; in[x] = 1; rec(i + 1, x + 1); in[x] = 0; } }
int main(int argc, char **argv) { N = atoi(argv[1]); s = atoi(argv[2]);
  rec(0, 1);
  printf("N=%d s=%d maxV=%d floor(2N/3)=%d  S={", N, s, best, 2 * N / 3);
  for (int k = 0; k < s; k++) printf(" %d", bestS[k]); printf(" }\n"); return 0; }

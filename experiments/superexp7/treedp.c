/* Composition trees with PROVEN instances of H only (experiments/superexp7/PROOFS.txt, 3).
   VQ[x]: the largest L such that a(x) is bounded below by a tree of compositions whose leaves
          are strips of size 2^l or 2^l + 1 with l >= L (so ln a(x) >= (x/6) ln(2^L/8)).
   VP[n]: the same for the pair (n, n+1) handled by ONE modulus per node.
   Moves (all proven in Lean, SuperExp7 / Live4):
     smooth q (prime factors <= 23), any residue: x -> classes floor(x/q), floor(x/q)+1;
     any q >= 2 with x mod q in {0, 1, q-1}.
   Usage: ./treedp.bin LOG2MAX [SMAX = largest smooth modulus used]           prints, per dyadic range, min over x of VQ[x]/log2(x)
   and the fraction of x with VQ[x] >= 0.40 / 0.45 log2(x)
   gcc -O2 -o treedp.bin treedp.c -lm */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
static int smooth(long q) {
  int ps[] = {2, 3, 5, 7, 11, 13, 17, 19, 23};
  for (int i = 0; i < 9; i++) while (q % ps[i] == 0) q /= ps[i];
  return q == 1;
}
int main(int argc, char **argv) {
  int K = atoi(argv[1]);
  long NM = 1L << K;
  long SMAX = argc > 2 ? atol(argv[2]) : 4096;
  signed char *VQ = calloc(NM + 2, 1), *VP = calloc(NM + 2, 1);
  /* smooth list */
  long *sm = malloc(sizeof(long) * 200000); int ns = 0;
  for (long q = 2; q <= SMAX && ns < 200000; q++) if (smooth(q)) sm[ns++] = q;
  /* smallest prime factor sieve for divisor enumeration */
  int *spf = calloc(NM + 2, sizeof(int));
  for (long i = 2; i <= NM + 1; i++) if (!spf[i]) for (long j = i; j <= NM + 1; j += i) if (!spf[j]) spf[j] = i;
  for (long x = 1; x <= NM; x++) {
    int vq = -100, vp = -100;
    int l = 0; while ((1L << (l + 1)) <= x) l++;
    if (x == (1L << l)) { vq = l; vp = l; }
    if (x == (1L << l) + 1) vq = l > vq ? l : vq;
    /* smooth moduli: x -> pair floor(x/q) (sizes floor, floor+1) */
    for (int i = 0; i < ns && sm[i] <= x; i++) {
      long n = x / sm[i];
      int v = (x % sm[i] == 0) ? VQ[n] : VP[n];
      if (v > vq) vq = v;
      long n1 = (x + 1) / sm[i];     /* pair (x, x+1): classes within floor(x/q)..+1 */
      int w = ((x + 1) % sm[i] == 0) ? VP[n1 - 1] : VP[n];
      if (w > vp) vp = w;
    }
    /* divisors of x, x-1, x+1 (residues 0, 1, q-1) */
    for (int t = -1; t <= 1; t++) {
      long y = x + t; if (y < 2) continue;
      /* enumerate divisors of y */
      long ds[4096]; int nd = 1; ds[0] = 1; long z = y;
      while (z > 1) { long p = spf[z]; int e = 0; while (z % p == 0) { z /= p; e++; }
        int cur = nd; long pk = 1; for (int k = 1; k <= e; k++) { pk *= p; for (int i = 0; i < cur; i++) ds[nd++] = ds[i] * pk; } }
      for (int i = 0; i < nd; i++) { long q = ds[i]; if (q < 2 || q > x) continue;
        if (t == 0) { int v = VQ[x / q]; if (v > vq) vq = v; v = VP[x / q]; if (v > vp) vp = v; } /* q | x: x -> n, x+1 -> (n, n+1) */
        if (t == -1) { int v = VP[(x - 1) / q]; if (v > vq) vq = v; }
        if (t == 1) { long n = (x + 1) / q - 1; if (n >= 1) { int v = VP[n]; if (v > vq) vq = v; if (v > vp) vp = v; } }
      }
    }
    VQ[x] = vq; VP[x] = vp;  /* VP refined below with Q(x) and Q(x+1) once x+1 known */
  }
  for (int k = 6; k <= K - 1; k++) {
    double worst = 1e9; long arg = 0; long g40 = 0, g45 = 0;
    for (long x = 1L << k; x < (1L << (k + 1)); x++) {
      double r = VQ[x] / log2((double)x);
      if (r < worst) { worst = r; arg = x; }
      if (r >= 0.40) g40++;
      if (r >= 0.45) g45++;
    }
    printf("x in [2^%d, 2^%d): min VQ/log2 x = %.3f at x = %ld; fraction with VQ >= 0.40 log2 x: %.3f, >= 0.45: %.3f\n",
           k, k + 1, worst, arg, g40 / (double)(1L << k), g45 / (double)(1L << k));
  }
  return 0;
}

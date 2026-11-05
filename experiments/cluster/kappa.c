/* Pair probabilities P(C_m and C_m') in floating point, for all pairs of an N-strip
   (or for abstract windows).  Same model as pair.py: times are iid U(0,1).
   For t_m = u < t_m' = v, each other element of U = W_m u W_m' is before u (prob u),
   between (prob v-u) or after (prob 1-v); the polynomial in (u,v) is integrated exactly
   by Gauss-Legendre after u = v*s.  2-D distribution of (D1, D2) by direct convolution.

   usage: kappa N            -> lines "m m' r r' P kappa" for all m<m' (r,r' >= 1)
          kappa -g m r m' r'  -> one abstract pair
*/
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

#define MAXQ 200
static double gx[MAXQ], gw[MAXQ];

static void gauleg(int n) { /* nodes/weights on [0,1] */
  for (int i = 0; i < n; i++) {
    double z = cos(M_PI * (i + 0.75) / (n + 0.5)), z1, pp;
    do {
      double p1 = 1, p2 = 0;
      for (int j = 1; j <= n; j++) { double p3 = p2; p2 = p1; p1 = ((2 * j - 1) * z * p2 - (j - 1) * p3) / j; }
      pp = n * (z * p1 - p2) / (z * z - 1);
      z1 = z; z = z1 - p1 / pp;
    } while (fabs(z - z1) > 1e-15);
    gx[i] = (1 - z) / 2; gw[i] = 1.0 / ((1 - z * z) * pp * pp);  /* weight on [0,1] = 2/(..)/2 */
  }
}

/* roles: role[x] in {+1,-1,0} for positions x in [lo,hi] */
static double ordered(int lo, int hi, int m, const int *ra, int mp, const int *rb, int r, int rp) {
  /* P(C_m and C_mp and m first).  ra = roles for C_m, rb for C_mp (indexed x-lo). */
  int n = 0, A[512], B[512];
  for (int x = lo; x <= hi; x++) {
    if (x == m || x == mp) continue;
    int a = ra[x - lo], b = rb[x - lo];
    if (a == 0 && b == 0) continue;
    A[n] = a; B[n] = b; n++;
  }
  int bm = rb[m - lo];
  int W1 = 2 * r + 1, W2 = 2 * rp + 3; /* D1 in [-r,r], D2 in [-rp-1, rp+1] */
  int Q = n / 2 + 3; if (Q > MAXQ) { fprintf(stderr, "Q too big\n"); exit(1); }
  gauleg(Q);
  double *cur = malloc(sizeof(double) * W1 * W2), *nxt = malloc(sizeof(double) * W1 * W2);
  double tot = 0;
  for (int iv = 0; iv < Q; iv++) for (int is = 0; is < Q; is++) {
    double v = gx[iv], u = v * gx[is];
    double pb = u, pm = v - u, pa = 1 - v;
    memset(cur, 0, sizeof(double) * W1 * W2);
    cur[(0 + r) * W2 + (bm + rp + 1)] = 1;
    for (int k = 0; k < n; k++) {
      memset(nxt, 0, sizeof(double) * W1 * W2);
      int a = A[k], b = B[k];
      for (int d1 = 0; d1 < W1; d1++) for (int d2 = 0; d2 < W2; d2++) {
        double c = cur[d1 * W2 + d2]; if (c == 0) continue;
        nxt[d1 * W2 + d2] += c * pa;
        int e2 = d2 + b; if (e2 >= 0 && e2 < W2) nxt[d1 * W2 + e2] += c * pm;
        int e1 = d1 + a; if (e1 >= 0 && e1 < W1 && e2 >= 0 && e2 < W2) nxt[e1 * W2 + e2] += c * pb;
      }
      double *t = cur; cur = nxt; nxt = t;
    }
    tot += gw[iv] * gw[is] * v * cur[r * W2 + rp + 1];
  }
  free(cur); free(nxt);
  return tot;
}

static double wal(int r) { double p = 1; for (int k = 1; k <= r; k++) p *= (2.0 * k) / (2.0 * k + 1); return p; }

static double pairp(int m, int r, int mp, int rp) {
  int lo = (m - r < mp - rp ? m - r : mp - rp), hi = (m + r > mp + rp ? m + r : mp + rp);
  int L = hi - lo + 1;
  int *ra = calloc(L, sizeof(int)), *rb = calloc(L, sizeof(int));
  for (int d = 1; d <= r; d++) { ra[m - d - lo] = 1; ra[m + d - lo] = -1; }
  for (int d = 1; d <= rp; d++) { rb[mp - d - lo] = 1; rb[mp + d - lo] = -1; }
  double p = ordered(lo, hi, m, ra, mp, rb, r, rp) + ordered(lo, hi, mp, rb, m, ra, rp, r);
  free(ra); free(rb);
  return p;
}

int main(int argc, char **argv) {
  if (argc > 1 && !strcmp(argv[1], "-g")) {
    int m = atoi(argv[2]), r = atoi(argv[3]), mp = atoi(argv[4]), rp = atoi(argv[5]);
    double p = pairp(m, r, mp, rp);
    printf("%.15g %.15g\n", p, p / (wal(r) * wal(rp)) - 1);
    return 0;
  }
  int N = atoi(argv[1]);
  for (int m = 1; m <= N; m++) for (int mp = m + 1; mp <= N; mp++) {
    int r = m - 1 < N - m ? m - 1 : N - m, rp = mp - 1 < N - mp ? mp - 1 : N - mp;
    if (r < 1 || rp < 1) continue;
    double p;
    if (m + r < mp - rp) p = wal(r) * wal(rp);
    else p = pairp(m, r, mp, rp);
    printf("%d %d %d %d %.15g %.15g\n", m, mp, r, rp, p, p / (wal(r) * wal(rp)) - 1);
  }
  return 0;
}

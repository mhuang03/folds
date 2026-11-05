/* cont.c: SMC for the CONTINUUM acceptance probabilities p_k = c_k / c_{k-1}.
 *
 * c_k = lim T(N,k)/N^k = probability that k i.i.d. uniform points of (0,1) form a valid
 * sequence.  Given valid x_1..x_{k-1}, the next point c is valid iff F(c) = 0, where
 *     F(c) = sum_i phi_{x_i}(c),  phi_x = -1 on (x/2, x),  +1 on (x, (1+x)/2),  0 elsewhere
 * (the dipole/arm picture, ../prefix/FINDINGS.txt section 3).  Z(x) = |{F = 0}| is the
 * acceptance probability, and p_k = E[Z(X_{k-1})] for X_{k-1} uniform on valid (k-1)-configs.
 *
 * SMC: M particles ~ uniform valid (k-1)-configs; p_k-hat = mean Z; resample prop. to Z
 * (systematic); extend each by a uniform point of {F = 0}.  prod p_k-hat is unbiased for c_K.
 * F is kept as a sorted list of breakpoints (pos, jump): x/2 (-1), x (+2), (1+x)/2 (-1).
 * Also reported: mean over particles of int F^2 (the continuum "imbalance variance").
 *
 * usage: cont K M seed   ->  lines "k p_hat log(c_k)_hat meanZ2 sdZ meanF2"
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

static uint64_t s[4];
static inline uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
static uint64_t nxt(void) {
    uint64_t r = rotl(s[1] * 5, 7) * 9, t = s[1] << 17;
    s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3]; s[2] ^= t; s[3] = rotl(s[3], 45);
    return r;
}
static double unif(void) { return (nxt() >> 11) * 0x1.0p-53; }

typedef struct { double p; int j; } bp;

static void insert(bp *a, int *n, double p, int j) {
    int lo = 0, hi = *n;
    while (lo < hi) { int mid = (lo + hi) / 2; if (a[mid].p < p) lo = mid + 1; else hi = mid; }
    memmove(a + lo + 1, a + lo, (*n - lo) * sizeof(bp));
    a[lo].p = p; a[lo].j = j; (*n)++;
}

/* measure of {F=0} and int F^2 */
static double zmeas(const bp *a, int n, double *f2) {
    double z = 0, q = 0, last = 0; int F = 0;
    for (int i = 0; i < n; i++) {
        double len = a[i].p - last;
        if (F == 0) z += len; else q += (double)F * F * len;
        F += a[i].j; last = a[i].p;
    }
    z += 1 - last;  /* F = 0 after the last breakpoint */
    *f2 = q;
    return z;
}

static double sample(const bp *a, int n, double z) {
    double u = unif() * z, last = 0; int F = 0;
    for (int i = 0; i < n; i++) {
        double len = a[i].p - last;
        if (F == 0) { if (u < len) return last + u; u -= len; }
        F += a[i].j; last = a[i].p;
    }
    return last + u;
}

int main(int argc, char **argv) {
    int K = atoi(argv[1]), M = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], 0, 10);
    s[0] = seed * 0x9E3779B97F4A7C15ULL + 1; s[1] = seed ^ 0xD1B54A32D192ED03ULL; s[2] = 7; s[3] = 11;
    for (int i = 0; i < 20; i++) nxt();
    int cap = 3 * K + 3;
    bp *A = malloc((size_t)M * cap * sizeof(bp)), *Bf = malloc((size_t)M * cap * sizeof(bp));
    int *n = calloc(M, sizeof(int)), *n2 = calloc(M, sizeof(int));
    double *Z = malloc(M * sizeof(double)), *cum = malloc(M * sizeof(double));
    double logc = 0;
    /* k = 1: one uniform point */
    for (int m = 0; m < M; m++) {
        double x = unif(); bp *a = A + (size_t)m * cap;
        insert(a, &n[m], x / 2, -1); insert(a, &n[m], x, 2); insert(a, &n[m], (1 + x) / 2, -1);
    }
    printf("1 1 0\n");
    for (int k = 2; k <= K; k++) {
        double tot = 0, tot2 = 0, f2t = 0;
        for (int m = 0; m < M; m++) {
            double f2;
            Z[m] = zmeas(A + (size_t)m * cap, n[m], &f2);
            tot += Z[m]; tot2 += Z[m] * Z[m]; f2t += f2;
        }
        double p = tot / M;
        if (p <= 0) { printf("# extinct at k=%d\n", k); break; }
        logc += log(p);
        printf("%d %.8f %.6f %.8f %.6f\n", k, p, logc, sqrt(tot2 / M - p * p), f2t / M);
        fflush(stdout);
        if (k == K) break;
        /* systematic resampling */
        double acc = 0;
        for (int m = 0; m < M; m++) { acc += Z[m]; cum[m] = acc; }
        double u0 = unif() * tot / M; int src = 0;
        for (int m = 0; m < M; m++) {
            double u = u0 + m * tot / M;
            while (src < M - 1 && cum[src] <= u) src++;
            memcpy(Bf + (size_t)m * cap, A + (size_t)src * cap, n[src] * sizeof(bp));
            n2[m] = n[src];
        }
        bp *t = A; A = Bf; Bf = t;
        int *tn = n; n = n2; n2 = tn;
        for (int m = 0; m < M; m++) {
            bp *a = A + (size_t)m * cap;
            double f2, z = zmeas(a, n[m], &f2);
            double x = sample(a, n[m], z);
            insert(a, &n[m], x / 2, -1); insert(a, &n[m], x, 2); insert(a, &n[m], (1 + x) / 2, -1);
        }
    }
    return 0;
}

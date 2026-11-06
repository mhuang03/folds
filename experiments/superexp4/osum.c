/* General slip sums on ANY N (odd N is the point): for every X ⊆ [N] with |X| = n1,
     T(X) = #{tau in V_{n1} : f_tau is a valid first block}      (strip-valid tau only)
     S(X) = #{sigma in V_{n2} : g_sigma valid on top of X}
   (Theorem A of superexp3: step conditions t~(kappa~(2 f_j - 1)) = 2 t(j - 1), resp.
   u~(lambda~(2 g_j - 1)) - 2u(j-1) = lambda~(2g_j-1) - (2j-1)).
   Prints sum_X T(X) S(X) / (a(n1) a(n2)) and the number of contributing X, and the
   same restricted to X with |X ∆ evens| <= 2*maxd (near-parity sets).
   usage: osum N n1 [maxd] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static double *cbuf;
static int okm(unsigned S, int m, int nn) {
    int r = m - 1 < nn - m ? m - 1 : nn - m;
    unsigned L = r ? (((1u << r) - 1) << (m - 1 - r)) : 0;
    unsigned R = r ? (((1u << r) - 1) << m) : 0;
    return __builtin_popcount(S & L) == __builtin_popcount(S & R);
}
static int cnt(unsigned S, int y, int nn) { /* cyclic count t~(y) */
    int a = y / nn, r = y % nn;
    unsigned mask = r ? ((1u << r) - 1) : 0;
    return a * __builtin_popcount(S) + __builtin_popcount(S & mask);
}
/* K[j]: the induced argument; mode 0: first block cond t~(K) = 2 t(j-1)
   mode 1: second block cond u~(L) - 2u(j-1) = L - (2j-1) */
static double count(int nn, int *K, int mode) {
    size_t NS = (size_t)1 << nn;
    memset(cbuf, 0, NS * sizeof(double));
    cbuf[0] = 1;
    for (size_t S = 0; S < NS; S++) if (cbuf[S])
        for (int m = 1; m <= nn; m++) {
            unsigned bit = 1u << (m - 1);
            if ((S & bit) || !okm(S, m, nn)) continue;
            int lhs = cnt(S, K[m], nn), t = cnt(S, m - 1, nn);
            int ok = mode == 0 ? (lhs == 2 * t) : (lhs - 2 * t == K[m] - (2 * m - 1));
            if (!ok) continue;
            cbuf[S | bit] += cbuf[S];
        }
    return cbuf[NS - 1];
}
int main(int argc, char **argv) {
    int N = atoi(argv[1]), n1 = atoi(argv[2]), n2 = N - n1;
    int maxd = argc > 3 ? atoi(argv[3]) : 1000;
    cbuf = malloc(((size_t)1 << (n1 > n2 ? n1 : n2)) * sizeof(double));
    int K[64], kap[64];
    for (int m = 0; m < 64; m++) K[m] = 2 * m - 1;
    double a1 = count(n1, K, 0), a2 = count(n2, K, 0);
    double sum = 0, sumNear = 0; long nX = 0, nNear = 0;
    for (unsigned long long M = 0; M < (1ULL << N); M++) {
        if (__builtin_popcountll(M) != n1) continue;
        kap[0] = 0;
        int f[64], g[64], nf = 0, ng = 0, dif = 0;
        for (int y = 1; y <= N; y++) {
            int in = M >> (y - 1) & 1;
            kap[y] = kap[y - 1] + in;
            if (in) f[++nf] = y; else g[++ng] = y;
            if (in != (y % 2 == 0)) dif++;
        }
        int KT[64], KS[64];
        for (int j = 1; j <= n1; j++) {
            int y = 2 * f[j] - 1, a = y / N, r = y % N;
            KT[j] = n1 * a + kap[r];
        }
        double T = count(n1, KT, 0);
        if (T == 0) continue;
        for (int j = 1; j <= n2; j++) {
            int y = 2 * g[j] - 1, a = y / N, r = y % N;
            KS[j] = n2 * a + (r - kap[r]);
        }
        double S = count(n2, KS, 1);
        if (S == 0) continue;
        sum += T * S; nX++;
        if (getenv("SHOW") && T * S / (a1 * a2) > atof(getenv("SHOW"))) { printf("%8.4f T=%.0f S=%.0f X=", T * S / (a1 * a2), T, S); for (int j = 1; j <= n1; j++) printf("%d ", f[j]); printf("\n"); }
        if (dif <= 2 * maxd + 1) { sumNear += T * S; nNear++; }
    }
    printf("N=%d n1=%d: a(n1)=%.0f a(n2)=%.0f  sum/(a a) = %.4f over %ld sets; near(<=%d swaps) %.4f over %ld\n",
           N, n1, a1, a2, sum / (a1 * a2), nX, maxd, sumNear / (a1 * a2), nNear);
    return 0;
}

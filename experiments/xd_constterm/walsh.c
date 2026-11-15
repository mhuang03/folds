// Walsh spectrum of S -> g(S) on the cube {0,1}^N and of the bridge function
// p(S) = g(S) g(S^c) (p / a(N) = probability that S is a prefix set of a random valid sequence).
//   ghat(T) = sum_S g(S) (-1)^{|S & T|}
// Prints, for f in {g, p}:  sum_{|T| = k} fhat(T)^2 / sum_T fhat(T)^2  for every degree k,
// the largest |fhat(T)| per degree, and the check
//   (N+1) a(N) = 2^{-N} sum_T (-1)^{|T|} ghat(T)^2.
// Exact integer transforms (__int128); squares accumulated in long double.
// usage: walsh N [top]
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
typedef __int128 i128;

static void fwht(i128 *f, int N) {
    size_t n = (size_t)1 << N;
    for (size_t h = 1; h < n; h <<= 1)
        for (size_t i = 0; i < n; i += h << 1)
            for (size_t j = i; j < i + h; j++) {
                i128 x = f[j], y = f[j + h];
                f[j] = x + y; f[j + h] = x - y;
            }
}

static void show(uint32_t T, int N) {
    printf("{");
    int first = 1;
    for (int i = 0; i < N; i++) if (T >> i & 1) { printf(first ? "%d" : ",%d", i + 1); first = 0; }
    printf("}");
}

int main(int argc, char **argv) {
    int N = atoi(argv[1]);
    int top = argc > 2 ? atoi(argv[2]) : 3;
    size_t n = (size_t)1 << N;
    uint32_t full = (uint32_t)(n - 1);
    uint32_t Lm[32], Rm[32];
    for (int m = 1; m <= N; m++) {
        int r = (m - 1 < N - m) ? m - 1 : N - m;
        Lm[m - 1] = Rm[m - 1] = 0;
        for (int e = 1; e <= r; e++) { Lm[m - 1] |= 1u << (m - 1 - e); Rm[m - 1] |= 1u << (m - 1 + e); }
    }
    i128 *g = malloc(n * sizeof(i128)), *p = malloc(n * sizeof(i128));
    g[0] = 1;
    for (uint32_t S = 1; S <= full; S++) {
        i128 acc = 0; uint32_t T = S;
        while (T) {
            int i = __builtin_ctz(T); T &= T - 1;
            uint32_t P = S & ~(1u << i);
            if (__builtin_popcount(P & Lm[i]) == __builtin_popcount(P & Rm[i])) acc += g[P];
        }
        g[S] = acc;
    }
    long double aN = (long double)g[full];
    for (uint32_t S = 0; S <= full; S++) { p[S] = g[S] * g[full ^ S]; if (S == full) break; }
    // layer-normalised version: q(S) = g(S) g(S^c) restricted to the middle layer |S| = N/2
    printf("N=%d a(N)=%.0Lf\n", N, aN);
    for (int which = 0; which < 3; which++) {
        i128 *f = which == 0 ? g : p;
        const char *name = which == 0 ? "g(S)" : which == 1 ? "p(S)=g(S)g(S^c)" : "p(S) on the middle layer |S|=floor(N/2)";
        if (which == 2) {
            for (uint32_t S = 0; S <= full; S++) {
                p[S] = (__builtin_popcount(S) == N / 2) ? g[S] * g[full ^ S] : 0;
                if (S == full) break;
            }
        }
        fwht(f, N);
        long double W[33] = {0}, tot = 0, alt = 0, mx[33] = {0};
        uint32_t arg[33] = {0};
        for (uint32_t T = 0; T <= full; T++) {
            long double v = (long double)f[T];
            int k = __builtin_popcount(T);
            W[k] += v * v; tot += v * v; alt += (k & 1 ? -1 : 1) * v * v;
            if (fabsl(v) > mx[k]) { mx[k] = fabsl(v); arg[k] = T; }
            if (T == full) break;
        }
        printf("-- Walsh spectrum of %s\n", name);
        if (which == 0)
            printf("   check: 2^-N sum (-1)^|T| ghat^2 / ((N+1) a(N)) = %.12Lf\n", alt / (long double)n / ((N + 1) * aN));
        printf("   degree  weight-fraction   cumulative   max|fhat|/fhat(0)   argmax\n");
        long double cum = 0, f0 = fabsl((long double)f[0]);
        for (int k = 0; k <= N; k++) {
            cum += W[k] / tot;
            printf("   %2d  %.6Le  %.8Lf  %.6Le  ", k, W[k] / tot, cum, mx[k] / f0);
            show(arg[k], N); printf("\n");
        }
        // top characters of degree 1..4 by |fhat|
        if (top > 0) {
            for (int k = 1; k <= 4 && k <= N; k++) {
                printf("   top degree-%d characters (fhat/fhat(0)):", k);
                // simple selection: repeated max scan
                uint32_t used[16]; int nu = 0;
                for (int t = 0; t < top; t++) {
                    long double best = -1; uint32_t bt = 0;
                    for (uint32_t T = 1; T <= full; T++) {
                        if (__builtin_popcount(T) == k) {
                            int skip = 0;
                            for (int u = 0; u < nu; u++) if (used[u] == T) skip = 1;
                            long double v = fabsl((long double)f[T]);
                            if (!skip && v > best) { best = v; bt = T; }
                        }
                        if (T == full) break;
                    }
                    if (best < 0) break;
                    used[nu++] = bt;
                    printf(" "); show(bt, N); printf(":%+.4Lf", (long double)f[bt] / f0);
                }
                printf("\n");
            }
        }
        fwht(f, N);   // undo (up to factor 2^N)
        for (uint32_t S = 0; S <= full; S++) { f[S] /= (i128)n; if (S == full) break; }
    }
    return 0;
}

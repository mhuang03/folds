// One-variable specialisations of F_N(z) = sum_pi prod_m z_m^{D_m(pi)}.
//   mode 0:  sum_pi q^{sum_m (D_m + r_m)}      (Laurent polynomial shifted by sum r_m)
//   mode 1:  sum_pi q^{sum_m |D_m|}
//   mode 2:  sum_pi q^{sum_m D_m^2}
//   mode 3:  sum_pi q^{#{m : D_m != 0}}         (defect count)
// Subset DP with polynomial values (u64 coefficients, fine for N <= 20).
// usage: polydp N mode      -> prints "N mode deg : c_0 c_1 ... c_deg"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef uint64_t u64;

int main(int argc, char **argv) {
    int N = atoi(argv[1]), mode = atoi(argv[2]);
    uint32_t Lm[32], Rm[32]; int rr[32], E[32], deg = 0;
    for (int m = 1; m <= N; m++) {
        int r = (m - 1 < N - m) ? m - 1 : N - m;
        rr[m - 1] = r; Lm[m - 1] = Rm[m - 1] = 0;
        for (int e = 1; e <= r; e++) { Lm[m - 1] |= 1u << (m - 1 - e); Rm[m - 1] |= 1u << (m - 1 + e); }
        E[m - 1] = mode == 0 ? 2 * r : mode == 1 ? r : mode == 2 ? r * r : (r > 0);
        deg += E[m - 1];
    }
    int W = deg + 1;
    uint32_t full = (1u << N) - 1;
    u64 *g = calloc((size_t)W << N, sizeof(u64));
    if (!g) { fprintf(stderr, "alloc\n"); return 1; }
    int *dg = calloc((size_t)1 << N, sizeof(int));   // degree bound of g[S]
    g[0] = 1;
    for (uint32_t S = 1; S <= full; S++) {
        u64 *out = g + (size_t)S * W;
        int dmax = 0;
        uint32_t T = S;
        while (T) {
            int i = __builtin_ctz(T); T &= T - 1;
            uint32_t P = S & ~(1u << i);
            int D = __builtin_popcount(P & Lm[i]) - __builtin_popcount(P & Rm[i]);
            int e = mode == 0 ? D + rr[i] : mode == 1 ? abs(D) : mode == 2 ? D * D : (D != 0);
            const u64 *in = g + (size_t)P * W;
            int dp = dg[P];
            for (int j = 0; j <= dp; j++) out[j + e] += in[j];
            if (dp + e > dmax) dmax = dp + e;
        }
        dg[S] = dmax;
    }
    u64 *res = g + (size_t)full * W;
    printf("%d %d %d :", N, mode, deg);
    for (int j = 0; j <= deg; j++) printf(" %llu", (unsigned long long)res[j]);
    printf("\n");
    return 0;
}

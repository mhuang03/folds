// Mod-d relaxations a_d(N) = #{perm : D_m == 0 (mod d) for every step}.
// d = 0 means the exact condition D_m = 0 (gives a(N)).
// Subset DP g[S] = sum_{m in S, d | D(S\m, m)} g[S\m];  one core, 2^N * 16 bytes.
// usage: apdp Nmax d1 d2 ...       (prints a table row per N)
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;

static void pr(u128 x) {
    char buf[64]; int i = 63; buf[i] = 0;
    if (x == 0) buf[--i] = '0';
    while (x) { buf[--i] = '0' + (int)(x % 10); x /= 10; }
    printf("%s", buf + i);
}

int main(int argc, char **argv) {
    int Nmax = atoi(argv[1]);
    u128 *g = malloc(sizeof(u128) << Nmax);
    for (int N = 1; N <= Nmax; N++) {
        uint32_t Lm[32], Rm[32];
        for (int m = 1; m <= N; m++) {
            int r = (m - 1 < N - m) ? m - 1 : N - m;
            Lm[m - 1] = Rm[m - 1] = 0;
            for (int e = 1; e <= r; e++) { Lm[m - 1] |= 1u << (m - 1 - e); Rm[m - 1] |= 1u << (m - 1 + e); }
        }
        printf("%d", N);
        for (int a = 2; a < argc; a++) {
            int d = atoi(argv[a]);
            uint32_t full = (N == 32) ? ~0u : ((1u << N) - 1);
            g[0] = 1;
            for (uint32_t S = 1; S <= full; S++) {
                u128 acc = 0;
                uint32_t T = S;
                while (T) {
                    int i = __builtin_ctz(T); T &= T - 1;
                    uint32_t P = S & ~(1u << i);
                    int D = __builtin_popcount(P & Lm[i]) - __builtin_popcount(P & Rm[i]);
                    if (d == 0 ? D == 0 : D % d == 0) acc += g[P];
                }
                g[S] = acc;
                if (S == full) break;
            }
            printf(" "); pr(g[full]);
        }
        printf("\n"); fflush(stdout);
    }
    return 0;
}

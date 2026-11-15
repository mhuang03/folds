// E(j) = c(2j) = g_N([1,2j]) (N >= 4j-1): the number of valid orderings of the interval
// [1,2j] at the left end of a long strip, computed with a 2^j subset DP.
//
// Reduction [proven, NOTES section 5]: in such an ordering the upper elements j+1..2j occupy
// the odd times in decreasing order, and the lower elements [1,j] occupy the even times in an
// order tau such that, for the i-th element m of tau with earlier lower set S (|S| = i-1),
//     |S & [m+1, min(2m-1,j)]| + max(0, 2m + i - 2j - 1) = |S & [1,m-1]|.
// Also prints the full c(d) for d <= 2*jmax via c(2j+1) = c(j), c(2j) = E(j).
// usage: prefix_even jmax
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
    int jmax = atoi(argv[1]);
    u128 *g = malloc(sizeof(u128) << jmax);
    static u128 E[64], c[130];
    E[0] = 1;
    for (int j = 1; j <= jmax; j++) {
        uint32_t Lm[32], Rm[32];
        for (int m = 1; m <= j; m++) {
            Lm[m - 1] = (1u << (m - 1)) - 1; Rm[m - 1] = 0;
            for (int x = m + 1; x <= 2 * m - 1 && x <= j; x++) Rm[m - 1] |= 1u << (x - 1);
        }
        uint32_t full = (1u << j) - 1;
        g[0] = 1;
        for (uint32_t S = 1; S <= full; S++) {
            u128 acc = 0; uint32_t T = S;
            int i = __builtin_popcount(S);       // the element removed is the i-th of tau
            while (T) {
                int k = __builtin_ctz(T); T &= T - 1;
                uint32_t P = S & ~(1u << k);
                int m = k + 1;
                int e = 2 * m + i - 2 * j - 1; if (e < 0) e = 0;
                if (__builtin_popcount(P & Rm[k]) + e == __builtin_popcount(P & Lm[k])) acc += g[P];
            }
            g[S] = acc;
        }
        E[j] = g[full];
        printf("E %d ", j); pr(E[j]); printf("\n"); fflush(stdout);
    }
    c[0] = 1;
    for (int d = 1; d <= 2 * jmax; d++) c[d] = (d & 1) ? c[d / 2] : E[d / 2];
    for (int d = 1; d <= 2 * jmax; d++) { printf("c %d ", d); pr(c[d]); printf("\n"); }
    return 0;
}

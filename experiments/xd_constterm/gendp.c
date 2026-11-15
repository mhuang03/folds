// Generic subset DP over permutations of [N] with arm variants and step tests.
//   arms:  true    L(m) = [m-r, m-1], R(m) = [m+1, m+r], r = min(m-1, N-m)
//          left    as true, but only m <= (N+1)/2 constrained
//          prefix  L(m) = [1, m-1], R(m) = [m+1, min(2m-1, N)]   (= g_M([1,N]) for M >= 2N+1:
//                  orderings of the interval [1,N] at the left end of a long strip)
//          radR    r = min(m-1, N-m, R)
//   test:  exact   D = 0                      -> count
//          modD    D == 0 (mod D)             -> count
//          sign    no restriction, weight (-1)^D   -> signed count  sum_pi (-1)^{sum_m D_m}
//          signfirst  as sign, but also prints the signed count by first panel
// usage: gendp arms test Nmin Nmax
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
typedef __int128 i128;

static void pr(i128 x) {
    char buf[64]; int i = 63; buf[i] = 0; int neg = x < 0; if (neg) x = -x;
    if (x == 0) buf[--i] = '0';
    while (x) { buf[--i] = '0' + (int)(x % 10); x /= 10; }
    if (neg) buf[--i] = '-';
    printf("%s", buf + i);
}

int main(int argc, char **argv) {
    const char *arms = argv[1], *test = argv[2];
    int Nmin = atoi(argv[3]), Nmax = atoi(argv[4]);
    int mod = 0, sign = 0, R = 1000;
    if (!strncmp(test, "mod", 3)) mod = atoi(test + 3);
    if (!strncmp(test, "sign", 4)) sign = 1;
    if (!strncmp(arms, "rad", 3)) R = atoi(arms + 3);
    i128 *g = malloc(sizeof(i128) << Nmax);
    for (int N = Nmin; N <= Nmax; N++) {
        uint32_t Lm[32], Rm[32];
        for (int m = 1; m <= N; m++) {
            Lm[m - 1] = Rm[m - 1] = 0;
            if (!strcmp(arms, "prefix")) {
                for (int x = 1; x < m; x++) Lm[m - 1] |= 1u << (x - 1);
                for (int x = m + 1; x <= 2 * m - 1 && x <= N; x++) Rm[m - 1] |= 1u << (x - 1);
                continue;
            }
            int r = (m - 1 < N - m) ? m - 1 : N - m;
            if (r > R) r = R;
            if (!strcmp(arms, "left") && 2 * m > N + 1) r = 0;
            for (int e = 1; e <= r; e++) { Lm[m - 1] |= 1u << (m - 1 - e); Rm[m - 1] |= 1u << (m - 1 + e); }
        }
        uint32_t full = (1u << N) - 1;
        g[0] = 1;
        for (uint32_t S = 1; S <= full; S++) {
            i128 acc = 0; uint32_t T = S;
            while (T) {
                int i = __builtin_ctz(T); T &= T - 1;
                uint32_t P = S & ~(1u << i);
                int D = __builtin_popcount(P & Lm[i]) - __builtin_popcount(P & Rm[i]);
                if (sign) acc += (D & 1) ? -g[P] : g[P];
                else if (mod ? D % mod == 0 : D == 0) acc += g[P];
            }
            g[S] = acc;
        }
        printf("%d ", N); pr(g[full]); printf("\n"); fflush(stdout);
    }
    return 0;
}

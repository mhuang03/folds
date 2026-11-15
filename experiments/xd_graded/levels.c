/* levels.c: rank statistics of the graded graph Gamma_N.
 *
 *   gcc -O2 -o bin/levels levels.c ;  bin/levels N
 *
 * For every rank k prints
 *   all/reach/live : number of subsets, reachable sets (g > 0), live sets (g(S) g(S^c) > 0)
 *   e_all/e_reach/e_live : number of edges from rank k to rank k+1 inside each vertex set
 *   T   = sum g(S)          (number of valid k-prefixes)
 *   Q   = sum g(S)^2        (closed walks  0 -> rank k -> 0, i.e. <0| D^k U^k |0>)
 *   A   = sum g(S) g(S^c)   (= a(N) for every k)
 *   dia = number of pairs (R, {a,b}), |R| = k, such that both orders a,b and b,a are valid
 *   one = number of pairs (R, {a,b}) such that exactly one of the two orders is valid
 *   (so the 2-step chain count from rank k to k+2 is 2 dia + one)
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

typedef unsigned __int128 u128;

static void pr128(u128 x) {
    char buf[64]; int n = 0;
    if (x == 0) { printf("0"); return; }
    while (x) { buf[n++] = '0' + (int)(x % 10); x /= 10; }
    while (n) putchar(buf[--n]);
}

int main(int argc, char **argv) {
    int N = atoi(argv[1]);
    uint32_t L[40], R[40];
    for (int m = 1; m <= N; m++) {
        int r = m - 1 < N - m ? m - 1 : N - m;
        L[m] = R[m] = 0;
        for (int d = 1; d <= r; d++) { L[m] |= 1u << (m - d - 1); R[m] |= 1u << (m + d - 1); }
    }
    uint32_t tot = 1u << N, full = tot - 1;
    uint64_t *g = calloc(tot, sizeof(uint64_t));
    g[0] = 1;
    for (uint32_t S = 1; S < tot; S++) {
        uint64_t t = 0;
        for (uint32_t x = S; x; x &= x - 1) {
            int m = __builtin_ctz(x) + 1;
            uint32_t T = S & ~(1u << (m - 1));
            if (__builtin_popcount(T & L[m]) == __builtin_popcount(T & R[m])) t += g[T];
        }
        g[S] = t;
    }
    static uint64_t nall[41], nreach[41], nlive[41], eall[41], ereach[41], elive[41], dia[41], one[41];
    static u128 Tk[41], Qk[41], Ak[41];
    for (uint32_t S = 0; S < tot; S++) {
        int k = __builtin_popcount(S);
        int rs = g[S] > 0, ls = rs && g[full ^ S] > 0;
        nall[k]++; nreach[k] += rs; nlive[k] += ls;
        Tk[k] += g[S]; Qk[k] += (u128)g[S] * g[S]; Ak[k] += (u128)g[S] * g[full ^ S];
        uint32_t val = 0;  /* valid additions */
        for (int m = 1; m <= N; m++) {
            uint32_t b = 1u << (m - 1);
            if (S & b) continue;
            if (__builtin_popcount(S & L[m]) == __builtin_popcount(S & R[m])) {
                val |= b;
                uint32_t T = S | b;
                eall[k]++;
                if (rs) ereach[k]++;           /* T is then reachable too */
                if (ls && g[full ^ T] > 0) elive[k]++;
            }
        }
        for (int a = 1; a <= N; a++) {
            uint32_t ba = 1u << (a - 1);
            if (S & ba) continue;
            for (int b = a + 1; b <= N; b++) {
                uint32_t bb = 1u << (b - 1);
                if (S & bb) continue;
                int ab = (val & ba) && __builtin_popcount((S | ba) & L[b]) == __builtin_popcount((S | ba) & R[b]);
                int ba_ = (val & bb) && __builtin_popcount((S | bb) & L[a]) == __builtin_popcount((S | bb) & R[a]);
                if (ab && ba_) dia[k]++; else if (ab || ba_) one[k]++;
            }
        }
    }
    printf("N=%d a=%llu\n", N, (unsigned long long)g[full]);
    printf("  k all reach live e_all e_reach e_live dia one T Q A\n");
    for (int k = 0; k <= N; k++) {
        printf("  %d %llu %llu %llu %llu %llu %llu %llu %llu ", k,
               (unsigned long long)nall[k], (unsigned long long)nreach[k], (unsigned long long)nlive[k],
               (unsigned long long)eall[k], (unsigned long long)ereach[k], (unsigned long long)elive[k],
               (unsigned long long)dia[k], (unsigned long long)one[k]);
        pr128(Tk[k]); putchar(' '); pr128(Qk[k]); putchar(' '); pr128(Ak[k]); putchar('\n');
    }
    return 0;
}

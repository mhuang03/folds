/* For every X ⊆ [N] with |X| = n1: the interval conditions of Theorem A (superexp3):
   first block j: elements z in the interval between K_j = kappa~(2f_j - 1) and 2j - 1
   (mod* n1) must come after j  -> cT = sum_j |K_j - (2j-1)|  (conditions on tau)
   second block j: interval between L_j = lambda~(2g_j - 1) and 2j - 1 (mod* n2) must come
   before j (impossible if it contains j or is longer than n2) -> cS = sum_j |L_j - (2j-1)|.
   Prints, by (cT, cS), the number of X, and lists X with cT <= A and cS <= B.
   usage: conds N n1 A B */
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
    int N = atoi(argv[1]), n1 = atoi(argv[2]), A = atoi(argv[3]), B = atoi(argv[4]);
    int n2 = N - n1;
    static long hist[64][64];
    for (unsigned long long M = 0; M < (1ULL << N); M++) {
        if (__builtin_popcountll(M) != n1) continue;
        int kap[64], f[64], g[64], nf = 0, ng = 0;
        kap[0] = 0;
        for (int y = 1; y <= N; y++) {
            int in = M >> (y - 1) & 1;
            kap[y] = kap[y - 1] + in;
            if (in) f[++nf] = y; else g[++ng] = y;
        }
        int cT = 0, cS = 0, bad = 0;
        char buf[2048]; int bl = 0;
        for (int j = 1; j <= n1; j++) {
            int y = 2 * f[j] - 1, a = y / N, r = y % N;
            int K = n1 * a + kap[r], d = K - (2 * j - 1);
            if (d) {
                int lo = d > 0 ? 2 * j - 1 : K, hi = d > 0 ? K : 2 * j - 1;
                for (int z = lo + 1; z <= hi; z++) {
                    int zz = (z - 1) % n1 + 1;
                    if (zz == j) continue;
                    bl += sprintf(buf + bl, "T%d<%d ", j, zz);
                }
                cT += abs(d);
            }
        }
        for (int j = 1; j <= n2; j++) {
            int y = 2 * g[j] - 1, a = y / N, r = y % N;
            int L = n2 * a + (r - kap[r]), d = L - (2 * j - 1);
            if (d) {
                int lo = d > 0 ? 2 * j - 1 : L, hi = d > 0 ? L : 2 * j - 1;
                if (hi - lo > n2) bad = 1;
                for (int z = lo + 1; z <= hi; z++) {
                    int zz = (z - 1) % n2 + 1;
                    if (zz == j) bad = 1;
                    bl += sprintf(buf + bl, "S%d<%d ", zz, j);
                }
                cS += abs(d);
            }
        }
        if (bad) continue;
        if (cT < 64 && cS < 64) hist[cT][cS]++;
        if (cT <= A && cS <= B) {
            printf("X=");
            for (int j = 1; j <= n1; j++) printf("%d,", f[j]);
            printf("  cT=%d cS=%d  %s\n", cT, cS, buf);
        }
    }
    for (int a = 0; a < 12; a++) {
        for (int b = 0; b < 12; b++) printf("%6ld", hist[a][b]);
        printf("\n");
    }
}

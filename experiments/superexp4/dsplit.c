/* Free splits: X ⊆ [N], |X| = p, such that "X in any valid order, then X^c in any valid
   order" is always valid (zero defect for both blocks, Theorem A of superexp3):
     first block:  kappa~(2 f_j - 1) = 2j - 1      for every j in [1,p]
     second block: lambda~(2 g_j - 1) = 2j - 1     for every j in [1,N-p]
   kappa~(N a + r) = p a + kappa(r).   Print, for each N, the sizes p admitting such X
   and the sets.   usage: dsplit Nmax  */
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
    int Nmax = atoi(argv[1]);
    for (int N = 2; N <= Nmax; N++) {
        int cnt[64] = {0};
        for (unsigned long X = 0; X < (1UL << N); X++) {
            int k[64]; k[0] = 0;
            int p = 0;
            for (int y = 1; y <= N; y++) { if (X >> (y - 1) & 1) p++; k[y] = p; }
            if (p == 0 || p == N) continue;
            int q = N - p, ok = 1, j1 = 0, j2 = 0;
            for (int x = 1; x <= N && ok; x++) {
                int y = 2 * x - 1, a = y / N, r = y % N;
                int kt = p * a + k[r], lt = q * a + (r - k[r]);
                if (X >> (x - 1) & 1) { j1++; if (kt != 2 * j1 - 1) ok = 0; }
                else { j2++; if (lt != 2 * j2 - 1) ok = 0; }
            }
            if (ok) {
                cnt[p]++;
                if (N <= 16 || cnt[p] <= 2) {
                    printf("N=%d p=%d X=", N, p);
                    for (int y = 1; y <= N; y++) if (X >> (y - 1) & 1) printf("%d,", y);
                    printf("\n");
                }
            }
        }
        printf("N=%d sizes:", N);
        for (int p = 1; p < N; p++) if (cnt[p]) printf(" %d(%d)", p, cnt[p]);
        printf("\n");
        fflush(stdout);
    }
}

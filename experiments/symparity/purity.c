/* f(N) = min over 3-AP-free permutations of [N] of the length of the longest
   constant-parity prefix.  For p = 1, 2, ...: search for a 3-AP-free permutation whose
   first p entries share a parity and whose entry p+1 has the other parity.
   Usage: purity Nmin Nmax */
#include <stdio.h>
#include <stdlib.h>

static int N, P, seq[64], placed[64], len;

/* placing m now is allowed iff no earlier x has its partner 2m-x in [1,N] unplaced */
static int ok(int m) {
    for (int t = 0; t < len; t++) {
        int y = 2 * m - seq[t];
        if (y >= 1 && y <= N && !placed[y]) return 0;
    }
    return 1;
}

static int rec(void) {
    if (len == N) return 1;
    for (int m = 1; m <= N; m++) {
        if (placed[m]) continue;
        if (len >= 1 && len < P && (m & 1) != (seq[0] & 1)) continue;
        if (len == P && (m & 1) == (seq[0] & 1)) continue;
        if (!ok(m)) continue;
        placed[m] = 1; seq[len++] = m;
        if (rec()) return 1;
        len--; placed[m] = 0;
    }
    return 0;
}

int main(int argc, char **argv) {
    int a = atoi(argv[1]), b = atoi(argv[2]);
    for (N = a; N <= b; N++) {
        for (P = 1; P < N; P++) {
            len = 0;
            for (int i = 0; i <= N; i++) placed[i] = 0;
            if (rec()) {
                printf("N=%d f=%d  floor((N+1)/4)=%d  example:", N, P, (N + 1) / 4);
                for (int i = 0; i < N; i++) printf(" %d", seq[i]);
                printf("\n");
                fflush(stdout);
                break;
            }
        }
    }
    return 0;
}

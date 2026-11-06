/* cluster.c -- is a cluster (cumulant) expansion over the constraints exact and sparse?
 *
 * For a set A of panels, Z(A) = number of permutations of [1..N] in which every panel
 * of A is a semi-symmetric step (the other panels are unconstrained).  Z(empty) = N!,
 * Z(all) = a(N).  Panels 1 and N have radius 0, so only the N-2 inner panels matter.
 * Log-cumulants (Moebius inversion over the Boolean lattice of constraint sets):
 *      ln Z(A) = sum_{B subset A} kappa(B),
 *      kappa(A) = sum_{B subset A} (-1)^{|A-B|} ln Z(B).
 * An exact expansion ln a(N) = sum_A kappa(A) is useful only if few kappa are nonzero.
 * Also tested: kappa(A) = 0 whenever A is disconnected in the INCOMPATIBILITY graph
 * (a, b incompatible unless their windows are disjoint or one window lies inside an
 * arm of the other: the exact independence case of Folds/Independence.lean).
 * Exact integer Z (u64, N <= 20 is safe); cumulants in long double.
 * usage: cluster.bin N
 */
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
typedef unsigned long long u64;
static int N;
static u64 lm[64], rm_[64];
static int lo[64], hi[64];
int main(int argc, char **argv) {
    N = atoi(argv[1]);
    for (int p = 0; p < N; p++) {
        int r = p < N - 1 - p ? p : N - 1 - p;
        lm[p] = rm_[p] = 0;
        for (int d = 1; d <= r; d++) { lm[p] |= 1ULL << (p - d); rm_[p] |= 1ULL << (p + d); }
        lo[p] = p - r; hi[p] = p + r;
    }
    int K = N - 2;                 /* inner panels p = 1..N-2 */
    u64 M = 1ULL << N, NA = 1ULL << K;
    u64 *dp = malloc(M * sizeof(u64));
    long double *L = malloc(NA * sizeof(long double));
    u64 *Z = malloc(NA * sizeof(u64));
    for (u64 A = 0; A < NA; A++) {
        u64 amask = A << 1;
        memset(dp, 0, M * sizeof(u64));
        dp[0] = 1;
        for (u64 s = 0; s < M; s++) {
            u64 v = dp[s];
            if (!v) continue;
            for (u64 t = (M - 1) & ~s; t; t &= t - 1) {
                int p = __builtin_ctzll(t);
                if ((amask >> p & 1) && __builtin_popcountll(s & lm[p]) != __builtin_popcountll(s & rm_[p])) continue;
                dp[s | (1ULL << p)] += v;
            }
        }
        Z[A] = dp[M - 1];
        L[A] = logl((long double)Z[A]);
    }
    printf("# N=%d a(N)=%llu N!=%llu\n", N, Z[NA - 1], Z[0]);
    /* Moebius transform */
    for (int i = 0; i < K; i++)
        for (u64 A = 0; A < NA; A++)
            if (A >> i & 1) L[A] -= L[A ^ (1ULL << i)];
    /* incompatibility graph on inner panels (index i <-> panel p = i+1) */
    u64 inc[64];
    for (int i = 0; i < K; i++) {
        inc[i] = 0;
        for (int j = 0; j < K; j++) {
            if (i == j) continue;
            int a = i + 1, b = j + 1;
            int disjoint = hi[a] < lo[b] || hi[b] < lo[a];
            /* window of a inside an arm of b (strictly left or right of centre b) */
            int inarm_ab = (lo[a] >= lo[b] && hi[a] < b) || (lo[a] > b && hi[a] <= hi[b]);
            int inarm_ba = (lo[b] >= lo[a] && hi[b] < a) || (lo[b] > a && hi[b] <= hi[a]);
            if (!(disjoint || inarm_ab || inarm_ba)) inc[i] |= 1ULL << j;
        }
    }
    long double tol = 1e-9L;
    long long nz[64] = {0}, tot[64] = {0}, conn[64] = {0}, nzdisc = 0;
    long double maxdisc = 0, sumk = 0;
    for (u64 A = 1; A < NA; A++) {
        int c = __builtin_popcountll(A);
        tot[c]++;
        /* connectivity of A in the incompatibility graph */
        u64 seen = A & -A, frontier = seen;
        while (frontier) {
            u64 nf = 0;
            for (u64 t = frontier; t; t &= t - 1) nf |= inc[__builtin_ctzll(t)] & A;
            nf &= ~seen;
            seen |= nf;
            frontier = nf;
        }
        int connected = seen == A;
        conn[c] += connected;
        int nonzero = fabsl(L[A]) > tol;
        nz[c] += nonzero;
        if (nonzero && !connected) { nzdisc++; if (fabsl(L[A]) > maxdisc) maxdisc = fabsl(L[A]); }
        sumk += L[A];
    }
    printf("# size  #sets  #connected(incompat.)  #nonzero kappa\n");
    long long T1 = 0, T2 = 0, T3 = 0;
    for (int c = 1; c <= K; c++) {
        printf("%2d %8lld %8lld %8lld\n", c, tot[c], conn[c], nz[c]);
        T1 += tot[c]; T2 += conn[c]; T3 += nz[c];
    }
    printf("TOTAL N=%d constraint-sets=%lld connected=%lld nonzero=%lld nonzero-but-disconnected=%lld (max %.3Le)\n", N, T1, T2, T3, nzdisc, maxdisc);
    printf("check: ln N! + sum kappa = %.12Lf, ln a(N) = %.12Lf\n", logl((long double)Z[0]) + sumk, logl((long double)Z[NA - 1]));
    return 0;
}

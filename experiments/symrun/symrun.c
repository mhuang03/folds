/* symrun.c -- Conjecture F' (the dyadic pattern of delta(N) = floor(N/2) - f(N)).

   Notation (see PROOFS.txt):
     ext(K,pi)   Theorem E test (../symstruct/PROOFS.txt section 2): is pi an extendable
                 prefix of a 3-AP-free permutation of [K]?
     G(K,a)      max length of an extendable prefix of [K] inside the top a values (DFS).
     Gr(K,L)     G(K, K-L) computed by the halving recursion (K,L) -> ((K+p)/2,(L+p)/2)
                 for K > KB, DFS below.
     g0(N)       G(floor(N/2), floor(N/2) - floor((N+1)/4))          (D = evens, u = 1)
     delta(N)    = g0(N) for N even, max(g0(N), g0(N+1) - 1) for N odd  (PROOFS.txt, Lemma 2)

   usage:  symrun base           G table for K <= 40 (2a <= K+1), recursion check K <= 72
           symrun brute N0 N1     exact f(N) by min over p, u of |D|-G(|D|,|A(u)|) (DFS only,
                                  all u, exact non-linked sets), compared with the formula
           symrun pattern Nmax    delta(N) by the formula vs Conjecture F' for 36 <= N <= Nmax
           symrun classes jmax    the class-invariance check (Lemma 4) for M = 2^j, j <= jmax
           symrun pairs Nmax      closed form (Lemma 3) vs recursion for N <= Nmax
           symrun wit K a len     print an extendable prefix of length len in top a of [K]  */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXV 160
#define KB 36

static int linkedK(int K, int y, int u) {
    int z1 = 2 * y - u, z2 = 2 * u - y;
    return (z1 >= 1 && z1 <= K) || (z2 >= 1 && z2 <= K);
}

static int ext(int K, const int *pi, int L) {
    if (L == 0 || K <= 1) return 1;
    int p = pi[0] & 1;
    int inpi[MAXV + 2];
    for (int v = 1; v <= K; v++) inpi[v] = 0;
    for (int i = 0; i < L; i++) inpi[pi[i]] = i + 1;
    for (int i = 0; i < L; i++) {
        int u = pi[i];
        if ((u & 1) == p) continue;
        for (int y = (p ? 1 : 2); y <= K; y += 2) {
            if (!linkedK(K, y, u)) continue;
            if (!inpi[y] || inpi[y] > i + 1) return 0;
        }
    }
    int a[MAXV], b[MAXV], la = 0, lb = 0;
    for (int i = 0; i < L; i++) {
        int v = pi[i], r = (v + 1) / 2;
        if ((v & 1) == p) a[la++] = r; else b[lb++] = r;
    }
    int KD = (K + p) / 2, KC = (K + 1 - p) / 2;
    return ext(KD, a, la) && ext(KC, b, lb);
}

static int gbest, gpi[MAXV], gwit[MAXV], gcap;
static void gdfs(int K, int lo, int hi, int L, int *used) {
    if (L > gbest) { gbest = L; memcpy(gwit, gpi, sizeof(int) * L); }
    if (gbest >= gcap) return;
    for (int v = lo; v <= hi; v++) {
        if (used[v]) continue;
        gpi[L] = v;
        if (!ext(K, gpi, L + 1)) continue;
        used[v] = 1; gdfs(K, lo, hi, L + 1, used); used[v] = 0;
        if (gbest >= gcap) return;
    }
}
static int Gmemo[MAXV + 1][MAXV + 1];
static int G(int K, int a) {          /* top a values */
    if (a <= 0) return 0;
    if (a > K) a = K;
    if (Gmemo[K][a] >= 0) return Gmemo[K][a];
    int used[MAXV + 2]; memset(used, 0, sizeof used);
    gbest = 0; gcap = 1000; gdfs(K, K - a + 1, K, 0, used);
    return Gmemo[K][a] = gbest;
}
static int Gbot(int K, int b) {
    if (b <= 0) return 0;
    int used[MAXV + 2]; memset(used, 0, sizeof used);
    gbest = 0; gcap = 1000; gdfs(K, 1, b, 0, used);
    return gbest;
}

/* G(K, K-L) by the recursion on (K, L) */
static long Gr(long K, long L) {
    /* the recursion tree, level by level, with duplicate states merged (at most 3 per
       level: Lemma 3), so this is O(log K) */
    long sk[64], sl[64], best = 0; int n = 1;
    sk[0] = K; sl[0] = L;
    while (n > 0) {
        long nk[64], nl[64]; int m = 0;
        for (int i = 0; i < n; i++) {
            long k = sk[i], l = sl[i];
            if (l >= k) continue;
            if (k <= KB) { long v = G((int)k, (int)(k - l)); if (v > best) best = v; continue; }
            long ck[2] = { (k + 1) / 2, k / 2 }, cl[2] = { (l + 1) / 2, l / 2 };
            for (int c = 0; c < 2; c++) {
                int dup = 0;
                for (int q = 0; q < m; q++) if (nk[q] == ck[c] && nl[q] == cl[c]) dup = 1;
                if (!dup) { nk[m] = ck[c]; nl[m] = cl[c]; m++; }
            }
        }
        if (m > 8) { fprintf(stderr, "more than 8 states at a level\n"); exit(1); }
        memcpy(sk, nk, sizeof(long) * m); memcpy(sl, nl, sizeof(long) * m); n = m;
    }
    return best;
}
static long g0(long N) { return Gr(N / 2, (N + 1) / 4); }
static long delta(long N) {
    long d = g0(N);
    if (N % 2 == 1) { long e = g0(N + 1) - 1; if (e > d) d = e; }
    return d;
}
static int conjF(long N) {   /* Conjecture F' for N >= 36 */
    long M = 1;
    while (72 * M <= N) M *= 2;
    if ((N >= 36 * M && N <= 40 * M + 1) || N == 40 * M + 3) return 4;
    if (N == 48 * M + 2 || (N >= 48 * M + 4 && N <= 56 * M - 2)) return 6;
    return 5;
}

/* closed form at level 2^j (Lemma 3): max over the <= 3 pairs */
static long closed(long K, long L, int j) {
    long M = 1L << j, X = K / M, r = K % M, Y = L / M, s = L % M, best = Gr(X, Y);
    if (r > 0 && s > 0) { long v = Gr(X + 1, Y + 1); if (v > best) best = v; }
    if (r > s) { long v = Gr(X + 1, Y); if (v > best) best = v; }
    if (s > r) { long v = Gr(X, Y + 1); if (v > best) best = v; }
    return best;
}

int main(int argc, char **argv) {
    memset(Gmemo, -1, sizeof Gmemo);
    if (argc < 2) return 1;
    if (!strcmp(argv[1], "base")) {
        for (int K = 1; K <= 40; K++) {
            printf("K=%2d:", K);
            for (int a = 1; 2 * a <= K + 1; a++) printf(" %d", G(K, a));
            printf("\n"); fflush(stdout);
        }
        long bad = 0, tot = 0;
        for (int K = 18; K <= 72; K++)
            for (int a = 1; 2 * a <= K + 1; a++) {
                int L = K - a;
                int r = G((K + 1) / 2, (K + 1) / 2 - (L + 1) / 2), s = G(K / 2, K / 2 - L / 2);
                int m = r > s ? r : s;
                tot++;
                if (m != G(K, a)) { bad++; printf("recursion fails K=%d a=%d G=%d rec=%d\n", K, a, G(K, a), m); }
            }
        printf("recursion check 18<=K<=72, 2a<=K+1: %ld cases, %ld failures\n", tot, bad);
        return 0;
    }
    if (!strcmp(argv[1], "brute")) {
        int N0 = atoi(argv[2]), N1 = atoi(argv[3]);
        long bad = 0;
        for (int N = N0; N <= N1; N++) {
            int best = 1 << 30;
            for (int p = 0; p < 2; p++) {
                int KD = (N + p) / 2;
                for (int u = (p ? 2 : 1); u <= N; u += 2) {
                    /* exact non-linked set, rescaled; check it is a top or bottom segment */
                    int lo = 1 << 30, hi = -1, cnt = 0;
                    for (int y = (p ? 1 : 2); y <= N; y += 2)
                        if (!linkedK(N, y, u)) { int r = (y + 1) / 2; cnt++; if (r < lo) lo = r; if (r > hi) hi = r; }
                    int g = 0;
                    if (cnt > 0) {
                        if (hi - lo + 1 != cnt) { printf("N=%d u=%d: A(u) not an interval\n", N, u); bad++; }
                        if (hi == KD) g = G(KD, cnt);
                        else if (lo == 1) g = Gbot(KD, cnt);
                        else { printf("N=%d u=%d: A(u) not a segment\n", N, u); bad++; }
                    }
                    if (KD - g < best) best = KD - g;
                }
            }
            long d = N / 2 - best;
            if (d != delta(N)) { bad++; printf("N=%d brute delta=%ld formula=%ld\n", N, d, delta(N)); }
            if (N >= 36 && d != conjF(N)) { bad++; printf("N=%d brute delta=%ld conj=%d\n", N, d, conjF(N)); }
        }
        printf("brute %d..%d: %ld problems\n", N0, N1, bad);
        return 0;
    }
    if (!strcmp(argv[1], "pattern")) {
        long Nm = atol(argv[2]), bad = 0, sec = 0;
        for (long N = 36; N <= Nm; N++) {
            if (delta(N) != conjF(N)) { bad++; if (bad < 20) printf("N=%ld delta=%ld conj=%d\n", N, delta(N), conjF(N)); }
            if (N % 2 && g0(N + 1) - 1 > g0(N)) sec++;
        }
        printf("pattern 36..%ld: %ld mismatches; second term decisive %ld times\n", Nm, bad, sec);
        return 0;
    }
    if (!strcmp(argv[1], "pairs")) {
        long Nm = atol(argv[2]), bad = 0;
        for (long N = 36; N <= Nm; N++)
            for (int j = 0; (36L << j) <= N; j++) {
                long K = N / 2, L = (N + 1) / 4;
                if ((K >> j) < 18) break;
                if (closed(K, L, j) != Gr(K, L)) { bad++; printf("N=%ld j=%d\n", N, j); }
            }
        printf("closed form vs recursion, N <= %ld: %ld failures\n", Nm, bad);
        return 0;
    }
    if (!strcmp(argv[1], "classes")) {
        /* Lemma 4: for M = 2^j >= 8, N = nM + t, delta(N) = delta(8n + t*) where
           t* = t (t <= 3), 4 (4 <= t <= M-2), 7 (t = M-1).  Check numerically. */
        int jm = atoi(argv[2]); long bad = 0, tot = 0;
        for (int j = 3; j <= jm; j++) {
            long M = 1L << j;
            for (long n = 36; n < 72; n++)
                for (long t = 0; t < M; t++) {
                    long ts = t <= 3 ? t : (t == M - 1 ? 7 : 4);
                    tot++;
                    if (delta(n * M + t) != delta(8 * n + ts)) { bad++; printf("j=%d n=%ld t=%ld\n", j, n, t); }
                }
        }
        printf("class invariance up to j=%d: %ld cases, %ld failures\n", jm, tot, bad);
        return 0;
    }
    if (!strcmp(argv[1], "wit")) {
        int K = atoi(argv[2]), a = atoi(argv[3]), len = atoi(argv[4]);
        int used[MAXV + 2]; memset(used, 0, sizeof used);
        gbest = 0; gcap = len; gdfs(K, K - a + 1, K, 0, used);
        if (gbest < len) { printf("none (max %d)\n", gbest); return 0; }
        printf("[");
        for (int i = 0; i < len; i++) printf("%s%d", i ? ", " : "", gwit[i]);
        printf("]\n");
        return 0;
    }
    return 0;
}

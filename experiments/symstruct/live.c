/* live.c -- extendability of prefixes of 3-AP-free permutations, and the exact
   minimal opening run f(N).

   THEOREM E (PROOFS.txt): a list pi of distinct elements of [K] (K >= 1) is a prefix of some
   3-AP-free permutation of [K] iff, with D' = the parity class of pi_1 and C' the other,
     (a) every linked pair y in D', u in C' that both occur in pi has y before u;
     (b) no u in C' occurring in pi is linked to a y in D' NOT occurring in pi;
     (c) pi restricted to D' (rescaled to [|D'|]) is extendable;
     (d) pi restricted to C' (rescaled to [|C'|]) is extendable.
   ("linked" inside [K]: 2y-u in [1,K] or 2u-y in [1,K].)  The empty prefix is extendable.
   This gives a polynomial test, used here (and cross-checked against brute force).

   G(K,a) = max length of an extendable prefix whose entries all lie in the top a values
            (K-a+1..K).  By reversal = max suffix inside the top a values; by the mirror the
            same for the bottom a values.
   f(N) = min over parities p, u in C_p of |D_p| - G(|D_p|, |A(u)|), A(u) = elements of D_p not
          linked to u (A(u) is always a top or bottom segment of D_p; checked).

   usage: live check Kmax        (cross-check Theorem E against brute force for K <= Kmax)
          live f Nmin Nmax        (print f(N), the late maximum, and a witness)
          live G Kmax             (table of G(K,a), a = floor(K/2) .. ) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAXV 512

static int linkedK(int K, int y, int u) {
    int z1 = 2 * y - u, z2 = 2 * u - y;
    return (z1 >= 1 && z1 <= K) || (z2 >= 1 && z2 <= K);
}

/* is pi[0..L-1] (distinct values in 1..K) an extendable prefix? */
static int ext(int K, const int *pi, int L) {
    if (L == 0 || K <= 2) return 1;
    int p = pi[0] & 1;
    static int inpi_buf[64][MAXV + 2];
    static int depth = 0;
    int *inpi = inpi_buf[depth];
    for (int v = 1; v <= K; v++) inpi[v] = 0;
    for (int i = 0; i < L; i++) inpi[pi[i]] = i + 1;
    /* (a) and (b) */
    for (int i = 0; i < L; i++) {
        int u = pi[i]; if ((u & 1) == p) continue;
        for (int y = (p ? 1 : 2); y <= K; y += 2) {
            if (!linkedK(K, y, u)) continue;
            if (!inpi[y] || inpi[y] > i + 1) return 0;
        }
    }
    /* (c), (d): D' values p,p+2,.. -> rank; rank of v in its class = (v+1)/2 for odd, v/2 even */
    int a[MAXV], b[MAXV], la = 0, lb = 0;
    for (int i = 0; i < L; i++) {
        int v = pi[i], r = (v + 1) / 2;
        if ((v & 1) == p) a[la++] = r; else b[lb++] = r;
    }
    int KD = p ? (K + 1) / 2 : K / 2, KC = K - KD;
    depth++;
    int ok = ext(KD, a, la) && ext(KC, b, lb);
    depth--;
    return ok;
}

/* ---------- brute force check: enumerate all 3-AP-free perms, mark extendable prefixes --- */
static int BK, bseq[32], bplaced[34], blen;
static long long nperm;
static int okstep(int m) {
    for (int t = 0; t < blen; t++) { int y = 2 * m - bseq[t]; if (y >= 1 && y <= BK && !bplaced[y]) return 0; }
    return 1;
}
/* returns 1 if this prefix extends; checks ext() at every stepwise-valid prefix */
static long long mism, tested;
static int brec(void) {
    int any = 0;
    if (blen == BK) { nperm++; any = 1; }
    else for (int m = 1; m <= BK; m++) {
        if (bplaced[m] || !okstep(m)) continue;
        bplaced[m] = 1; bseq[blen++] = m;
        int r = brec();
        blen--; bplaced[m] = 0;
        any |= r;
    }
    tested++;
    if (ext(BK, bseq, blen) != any) {
        mism++;
        if (mism < 10) { printf("mismatch K=%d ext=%d true=%d :", BK, !any, any); for (int i = 0; i < blen; i++) printf(" %d", bseq[i]); printf("\n"); }
    }
    return any;
}

/* ---------- G(K,a): DFS over extendable prefixes inside the top a values ---------- */
static int gbest, gpi[MAXV], gwit[MAXV];
static void gdfs(int K, int a, int L, int *used) {
    if (L > gbest) { gbest = L; memcpy(gwit, gpi, sizeof(int) * L); }
    for (int v = K - a + 1; v <= K; v++) {
        if (used[v]) continue;
        gpi[L] = v;
        if (!ext(K, gpi, L + 1)) continue;
        used[v] = 1; gdfs(K, a, L + 1, used); used[v] = 0;
    }
}
static int Gmemo[MAXV + 1][MAXV + 1];
static int G(int K, int a) {
    if (a <= 0) return 0;
    if (Gmemo[K][a] >= 0) return Gmemo[K][a];
    int used[MAXV + 2]; memset(used, 0, sizeof used);
    gbest = 0; gdfs(K, a, 0, used);
    return Gmemo[K][a] = gbest;
}

/* G by the halving recursion (THEOREM F: exact for K >= 33 and 2a <= K+3); DFS below. */
static long Grec(long K, long a) {
    if (a <= 0) return 0;
    if (K <= 32) return G((int)K, (int)a);
    long ao = 0, ae = 0, lo = K - a + 1;
    /* number of odd / even values in [lo, K] */
    ao = (K + 1) / 2 - lo / 2; ae = K / 2 - (lo - 1) / 2;
    long r1 = Grec((K + 1) / 2, ao), r2 = Grec(K / 2, ae);
    return r1 > r2 ? r1 : r2;
}

int main(int argc, char **argv) {
    memset(Gmemo, -1, sizeof Gmemo);
    if (!strcmp(argv[1], "check")) {
        int Km = atoi(argv[2]);
        for (BK = 1; BK <= Km; BK++) {
            nperm = 0; mism = 0; tested = 0; blen = 0; memset(bplaced, 0, sizeof bplaced);
            brec();
            printf("K=%d perms=%lld prefixes tested=%lld mismatches=%lld\n", BK, nperm, tested, mism);
            fflush(stdout);
        }
        /* also: all extendable prefixes are generated by stepwise-valid steps? check that
           every one-element prefix is extendable */
        return 0;
    }
    if (!strcmp(argv[1], "f")) {
        int N0 = atoi(argv[2]), N1 = atoi(argv[3]);
        for (int N = N0; N <= N1; N++) {
            int best = 1 << 30, late = 0, bp = -1, bu = -1, bg = 0, ba = 0;
            for (int p = 0; p < 2; p++) {
                int KD = 0, KC = 0;
                for (int v = 1; v <= N; v++) { if ((v & 1) == p) KD++; else KC++; }
                for (int u = 1; u <= N; u++) {
                    if ((u & 1) == p) continue;
                    /* A(u) in D-rank coordinates */
                    int lo = 1 << 30, hi = -1, cnt = 0;
                    for (int y = (p ? 1 : 2); y <= N; y += 2)
                        if (!linkedK(N, y, u)) { int r = (y + 1) / 2; cnt++; if (r < lo) lo = r; if (r > hi) hi = r; }
                    if (cnt && !(lo == 1 || hi == KD)) { printf("A(u) not a segment N=%d u=%d\n", N, u); }
                    if (cnt && hi - lo + 1 != cnt) printf("A(u) not contiguous N=%d u=%d\n", N, u);
                    /* u must be able to start a 3-AP-free perm of C: check */
                    int ur = (u + 1) / 2; int one[1] = { ur };
                    if (!ext(KC, one, 1)) { printf("u=%d cannot start\n", u); continue; }
                    int g = G(KD, cnt);
                    if (KD - g < best) { best = KD - g; bp = p; bu = u; bg = g; ba = cnt; }
                    if (g > late) late = g;
                }
            }
            printf("N=%d f=%d late=%d floor(N/2)-f=%d  (D=%s, u=%d, |A|=%d, G=%d)\n", N, best, late,
                   N / 2 - best, bp ? "odd" : "even", bu, ba, bg);
            fflush(stdout);
        }
        return 0;
    }
    if (!strcmp(argv[1], "G")) {
        /* table of G(K,a) for 2a <= K+3 by DFS, and a check of the halving recursion
           G(K,a) = max(G(ceil(K/2), #odd in top a), G(floor(K/2), #even in top a)) */
        int Km = atoi(argv[2]); int bad = 0;
        for (int K = 1; K <= Km; K++) {
            printf("K=%d:", K);
            for (int a = 1; 2 * a <= K + 3 && a <= K; a++) {
                int g = G(K, a);
                int ao = 0, ae = 0;
                for (int v = K - a + 1; v <= K; v++) { if (v & 1) ao++; else ae++; }
                int r1 = G((K + 1) / 2, ao), r2 = G(K / 2, ae);
                int r = r1 > r2 ? r1 : r2;
                printf(" %d%s", g, g == r ? "" : "*");
                if (g != r && K >= 31) bad++;
            }
            printf("\n"); fflush(stdout);
        }
        printf("recursion failures for K>=31: %d   (* marks K where G != halving recursion)\n", bad);
        return 0;
    }
    if (!strcmp(argv[1], "T")) {
        /* T_sym(N,k): stepwise-valid k-prefixes;  L_sym(N,k): extendable k-prefixes, k=2,3 */
        int N0 = atoi(argv[2]), N1 = atoi(argv[3]);
        for (int N = N0; N <= N1; N++) {
            long long T2 = 0, T3 = 0, L2 = 0, L3 = 0; int pi[3];
            for (int x = 1; x <= N; x++) for (int y = 1; y <= N; y++) {
                if (y == x) continue;
                int z = 2 * y - x; if (z >= 1 && z <= N) continue;   /* y needs partner of x */
                T2++; pi[0] = x; pi[1] = y; int e2 = ext(N, pi, 2); L2 += e2;
                for (int w = 1; w <= N; w++) {
                    if (w == x || w == y) continue;
                    int z1 = 2 * w - x, z2 = 2 * w - y;
                    if (z1 >= 1 && z1 <= N && z1 != y) continue;
                    if (z2 >= 1 && z2 <= N && z2 != x) continue;
                    T3++;
                    if (e2) { pi[2] = w; L3 += ext(N, pi, 3); }
                }
            }
            printf("%d %lld %lld %lld %lld\n", N, T2, T3, L2, L3); fflush(stdout);
        }
        return 0;
    }
    if (!strcmp(argv[1], "Tk")) {
        /* T_sym(N,k) and L_sym(N,k) by depth-first search over stepwise-valid prefixes */
        int k = atoi(argv[2]), N0 = atoi(argv[3]), N1 = atoi(argv[4]);
        for (int N = N0; N <= N1; N++) {
            long long T = 0, L = 0; int pi[16], used[MAXV + 2], d = 0, next[16];
            memset(used, 0, sizeof used); next[0] = 1;
            while (d >= 0) {
                if (d == k) { T++; L += ext(N, pi, k); d--; if (d >= 0) used[pi[d]] = 0; continue; }
                int m = next[d]; int found = 0;
                for (; m <= N; m++) {
                    if (used[m]) continue;
                    int okm = 1;
                    for (int t = 0; t < d && okm; t++) { int z = 2 * m - pi[t]; if (z >= 1 && z <= N && !used[z]) okm = 0; }
                    if (okm) { found = 1; break; }
                }
                if (!found) { d--; if (d >= 0) used[pi[d]] = 0; continue; }
                pi[d] = m; used[m] = 1; next[d] = m + 1; d++; next[d] = 1;
            }
            printf("%d %lld %lld\n", N, T, L); fflush(stdout);
        }
        return 0;
    }
    if (!strcmp(argv[1], "Lk")) {
        /* L_sym(N,j) for j = 1..k: DFS over extendable prefixes only */
        int k = atoi(argv[2]), N0 = atoi(argv[3]), N1 = atoi(argv[4]);
        for (int N = N0; N <= N1; N++) {
            long long cnt[17]; memset(cnt, 0, sizeof cnt);
            int pi[17], d = 0, next[17]; next[0] = 1; int used[MAXV + 2]; memset(used, 0, sizeof used);
            while (d >= 0) {
                if (d == k) { d--; used[pi[d]] = 0; continue; }
                int m = next[d], found = 0;
                for (; m <= N; m++) { if (used[m]) continue; pi[d] = m; if (ext(N, pi, d + 1)) { found = 1; break; } }
                if (!found) { d--; if (d >= 0) used[pi[d]] = 0; continue; }
                used[m] = 1; next[d] = m + 1; cnt[d + 1]++; d++; next[d] = 1;
            }
            printf("%d", N); for (int j = 1; j <= k; j++) printf(" %lld", cnt[j]); printf("\n"); fflush(stdout);
        }
        return 0;
    }
    if (!strcmp(argv[1], "frec")) {
        /* f(N) using the PROVEN halving recursion for K >= 31 (base: DFS for K <= 30) */
        long N0 = atol(argv[2]), N1 = atol(argv[3]);
        for (long N = N0; N <= N1; N++) {
            long best = 1L << 40; int bestp = -1;
            for (int p = 0; p < 2; p++) {
                long KD = p ? (N + 1) / 2 : N / 2;
                long amax = 0;
                /* the extreme C-elements have the largest non-linked sets (A(u) shrinks inwards) */
                long cand[2] = { p ? 2 : 1, (N % 2 != p) ? N : N - 1 };
                for (int c = 0; c < 2; c++) {
                    long u = cand[c], cnt = 0;
                    for (long y = (p ? 1 : 2); y <= N; y += 2) {
                        long z1 = 2 * y - u, z2 = 2 * u - y;
                        if (!((z1 >= 1 && z1 <= N) || (z2 >= 1 && z2 <= N))) cnt++;
                    }
                    if (cnt > amax) amax = cnt;
                }
                if (2 * amax > KD + 3) { printf("N=%ld outside region\n", N); }
                long g = Grec(KD, amax);
                if (KD - g < best) { best = KD - g; bestp = p; }
            }
            printf("N=%ld f=%ld delta=%ld D=%s\n", N, best, N / 2 - best, bestp ? "odd" : "even");
        }
        return 0;
    }
    return 0;
}

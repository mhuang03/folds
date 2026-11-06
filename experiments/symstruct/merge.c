/* merge.c -- the merge (shuffle) decomposition of 3-AP-free permutations of [n].

   THEOREM M (PROOFS.txt): fix a parity p, let D = values of parity p in [1,n] and C the
   others.  A permutation a with a_1 in D is 3-AP-free iff
     (i) its D-subsequence sigma and its C-subsequence tau are 3-AP-free, and
    (ii) every "linked" pair y in D, u in C (2y-u in [1,n] or 2u-y in [1,n]) has y before u.
   Hence theta(n) = sum_p sum_{sigma,tau} P(sigma,tau), P = number of admissible merges:
     P = #{ 0 <= c_1 <= ... <= c_{|C|} <= |D| : c_j >= M_j },  M_j = max_{i<=j} m(tau_i),
     m(u) = largest position (1-based) in sigma of a D-element linked to u.
   (c_j = number of D-elements before tau_j.)

   This program enumerates the 3-AP-free permutations of [|D|] and [|C|], compresses them to
   the data P depends on (sigma -> the vector m; tau -> its longest prefix inside
   U = {u : m(u) < |D| for some sigma}), and prints
     theta(n) (recomputed), r(n) = theta(n)/(2 theta(n/2-) theta(n/2+)), max P, the
     distribution of P, f(n) = min run (= min M_1), the late-D maximum max(|D| - M_1),
     |U|, numbers of classes.
   usage: merge n [verbose] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef unsigned __int128 u128;
#define MAXK 32

static int K;              /* size of the interval being enumerated */
static int seq[MAXK + 1], placed[MAXK + 2], len;
static void (*visit)(const int *s);

static int ok(int m) {
    for (int t = 0; t < len; t++) {
        int y = 2 * m - seq[t];
        if (y >= 1 && y <= K && !placed[y]) return 0;
    }
    return 1;
}
static void rec(void) {
    if (len == K) { visit(seq); return; }
    for (int m = 1; m <= K; m++) {
        if (placed[m] || !ok(m)) continue;
        placed[m] = 1; seq[len++] = m;
        rec();
        len--; placed[m] = 0;
    }
}
static void enumerate(int k, void (*f)(const int *)) {
    K = k; len = 0; memset(placed, 0, sizeof placed); visit = f;
    if (k == 0) { f(seq); return; }
    rec();
}

/* ---------- simple hash map: key = byte string of fixed max length ---------- */
#define KEYLEN 40
typedef struct { unsigned char key[KEYLEN]; int klen; uint64_t cnt; int used; } Ent;
typedef struct { Ent *t; size_t cap, n; } Map;
static uint64_t hsh(const unsigned char *k, int l) {
    uint64_t h = 1469598103934665603ULL;
    for (int i = 0; i < l; i++) { h ^= k[i]; h *= 1099511628211ULL; }
    return h ^ (uint64_t)l;
}
static void minit(Map *m, size_t cap) { m->cap = cap; m->n = 0; m->t = calloc(cap, sizeof(Ent)); }
static void madd(Map *m, const unsigned char *k, int l, uint64_t c) {
    if (2 * m->n >= m->cap) {
        Map o = *m; minit(m, o.cap * 2);
        for (size_t i = 0; i < o.cap; i++) if (o.t[i].used) madd(m, o.t[i].key, o.t[i].klen, o.t[i].cnt);
        free(o.t);
    }
    size_t i = hsh(k, l) & (m->cap - 1);
    while (m->t[i].used && !(m->t[i].klen == l && !memcmp(m->t[i].key, k, l))) i = (i + 1) & (m->cap - 1);
    if (!m->t[i].used) { m->t[i].used = 1; memcpy(m->t[i].key, k, l); m->t[i].klen = l; m->t[i].cnt = 0; m->n++; }
    m->t[i].cnt += c;
}

static int n, nD, nC, Dv[MAXK + 1], Cv[MAXK + 1];  /* Dv[i] = i-th D value (1-based) */
static int linked[MAXK + 1][MAXK + 1];               /* linked[i][j]: D_i ~ C_j */
static Map sigmap, taumap;
static int inU[MAXK + 1];

static void visit_sigma(const int *s) {
    unsigned char key[KEYLEN];
    int pos[MAXK + 1];
    for (int i = 0; i < nD; i++) pos[s[i]] = i + 1;
    for (int j = 1; j <= nC; j++) {
        int mx = 0;
        for (int i = 1; i <= nD; i++) if (linked[i][j] && pos[i] > mx) mx = pos[i];
        key[j - 1] = (unsigned char)mx;
    }
    madd(&sigmap, key, nC, 1);
}
static void visit_tau(const int *s) {
    unsigned char key[KEYLEN]; int l = 0;
    while (l < nC && inU[s[l]]) { key[l] = (unsigned char)s[l]; l++; }
    if (l > KEYLEN - 1) { fprintf(stderr, "tau prefix too long\n"); exit(1); }
    key[l] = (unsigned char)(l < nC ? 255 : 254); /* 255: a non-U element follows */
    madd(&taumap, key, l + 1, 1);
}

int main(int argc, char **argv) {
    n = atoi(argv[1]); int verbose = argc > 2;
    u128 total = 0; uint64_t maxP = 0; int fmin = 1 << 30, latemax = 0;
    uint64_t hist[4096]; memset(hist, 0, sizeof hist); u128 pairs = 0;
    for (int p = 0; p < 2; p++) {
        nD = nC = 0;
        for (int v = 1; v <= n; v++) { if (v % 2 == p) Dv[++nD] = v; else Cv[++nC] = v; }
        if (nD == 0) continue;
        if (nC == 0) { total += 1; continue; } /* n = 1 */
        for (int i = 1; i <= nD; i++) for (int j = 1; j <= nC; j++) {
            int y = Dv[i], u = Cv[j];
            linked[i][j] = (2 * y - u >= 1 && 2 * y - u <= n) || (2 * u - y >= 1 && 2 * u - y <= n);
        }
        minit(&sigmap, 1024); minit(&taumap, 1024);
        enumerate(nD, visit_sigma);
        memset(inU, 0, sizeof inU);
        for (size_t i = 0; i < sigmap.cap; i++) if (sigmap.t[i].used)
            for (int j = 1; j <= nC; j++) if (sigmap.t[i].key[j - 1] < nD) inU[j] = 1;
        int Usz = 0; for (int j = 1; j <= nC; j++) Usz += inU[j];
        enumerate(nC, visit_tau);
        if (verbose) {
            printf("p=%d |D|=%d |C|=%d sigma-classes=%zu tau-classes=%zu U={", p, nD, nC, sigmap.n, taumap.n);
            for (int j = 1; j <= nC; j++) if (inU[j]) printf(" %d", Cv[j]);
            printf(" }\n");
        }
        for (size_t a = 0; a < sigmap.cap; a++) if (sigmap.t[a].used) {
            const unsigned char *mv = sigmap.t[a].key;
            for (size_t b = 0; b < taumap.cap; b++) if (taumap.t[b].used) {
                const unsigned char *tk = taumap.t[b].key; int l = taumap.t[b].klen - 1;
                /* ways[c] = number of admissible (c_1..c_j) with c_j = c */
                uint64_t ways[MAXK + 2], nw[MAXK + 2];
                for (int c = 0; c <= nD; c++) ways[c] = 1; /* j = 0: virtual c_0 = 0 .. treat as any start */
                int M = 0;
                /* proper start: before tau_1, "c_0 = 0" */
                for (int c = 0; c <= nD; c++) ways[c] = (c == 0);
                for (int j = 0; j < l; j++) {
                    int mj = mv[tk[j] - 1]; if (mj > M) M = mj;
                    uint64_t acc = 0;
                    for (int c = 0; c <= nD; c++) { acc += ways[c]; nw[c] = c >= M ? acc : 0; }
                    memcpy(ways, nw, sizeof(uint64_t) * (nD + 1));
                    if (j == 0) {
                        if (M < fmin) fmin = M;
                        if (nD - M > latemax) latemax = nD - M;
                    }
                }
                uint64_t P = 0;
                for (int c = 0; c <= nD; c++) P += ways[c];  /* next element forced to c = |D| */
                if (l == 0) { /* first tau element not in U: run = |D| */
                    if (nD < fmin) fmin = nD;
                }
                uint64_t w = sigmap.t[a].cnt * taumap.t[b].cnt;
                total += (u128)w * P; pairs += w;
                if (P > maxP) maxP = P;
                if (P < 4096) hist[P] += w;
            }
        }
        free(sigmap.t); free(taumap.t);
    }
    printf("n=%d theta=%llu f=%d latemax=%d maxP=%llu  P-distribution:", n,
           (unsigned long long)total, fmin, latemax, (unsigned long long)maxP);
    for (int i = 0; i < 4096; i++) if (hist[i]) printf(" %d:%llu", i, (unsigned long long)hist[i]);
    printf("\n");
    return 0;
}

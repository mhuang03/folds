/* theta.c -- exact theta(n) = A003407(n) (number of 3-AP-free permutations of [1,n]) modulo
   several primes at once, by the window recursion of experiments/symratio/PROOFS.txt
   (Theorems W, S, J), reorganised so that the cost is ~ n^2 polylog per value:

   WINDOWS.  For a 3-AP-free permutation a of [x]: head(a) = first 6 entries,
   G(a) = reversed tail = (a_x, a_{x-1}, ..., a_{x-5}).  By reversal, the set of heads equals
   the set of reversed tails; call it W_x (sorted lexicographically).  For x >= 19,
       W_x  =  lift_0(W_{floor x/2})  u  lift_1(W_{ceil x/2}),    lift_p(g) = 2g - p
   (Theorem J: the head of a merged permutation is the lifted head of sigma, its tail the
   lifted tail of tau; possibly a superset of the realised windows, which is harmless).

   JOINT LAW.  J_x(H,G) = #{a : head H, reversed tail G} is a SYMMETRIC W_x x W_x matrix
   (reversal swaps the two windows).  Theorem J, written in this indexing: for x >= 19 and
   q = parity of the first entry, d = (x+q)/2, c = (x+1-q)/2,
       J_x(lift_q H', lift_{1-q} G') = [ J_d  Pi_{x,q}  J_c ](H', G'),
   Pi_{x,q}(G_s, H_t) = Pi_{x,q}(tail sigma, head tau) of Theorem W, rows indexed by the
   reversed tail of sigma (in W_d), columns by the head of tau (in W_c).
   Marginal t_x = J_x 1 (head law = reversed-tail law), and
       theta(x) = sum_q  t_d^T Pi_{x,q} t_c,
       t_x on lift_{1-q}(W_c) = J_c (Pi_{x,q}^T t_d)          (J_c applied recursively).
   We never form J_x for x > 18: L_x(v) = J_x v is evaluated recursively,
       L_x(v)|_{lift_{1-q} W_c} = L_c( Pi_{x,q}^T L_d( v|_{lift_q W_d} ) ),
   with the enumerated J_x (sparse) for 9 <= x <= 18.

   Pi BY A DOUBLE TRIE.  Write y'_1..y'_6 = lift_q of the reversed tail of sigma (y'_1 =
   last entry), u_1..u_6 = lift_{1-q} of the head of tau.  Theorem W's count is
       Pi = #{ Young diagrams lambda in the 6x6 box (rows i <-> u_i, columns k <-> y'_k)
               containing no cell (i,k) with y'_k, u_i linked }
   (lambda_i = number of y's after u_i in the interleaving).  If i0 = first i with
   linked(y'_1, u_i) and k0 = first k with linked(y'_k, u_1), only rows < i0 and columns
   < k0 can be used, so Pi depends only on y'_1..y'_{k0}, u_1..u_{i0}.  We walk the trie of
   W_d (rows) and the trie of W_c (columns) simultaneously and stop as soon as both
   closures are known; each stopped pair (S-node, T-node) adds Pi * (sum of the row weights
   below S-node) to an accumulator at T-node; the accumulators are pushed down at the end.
   (Pi = 1 iff y'_1, u_1 linked: a single pair of depth-1 nodes then covers a whole block.)

   ARITHMETIC.  K primes p < 2^61 in one process (the tries are shared); residues in
   Montgomery form; Pi * residue products accumulated lazily in unsigned __int128.

   Build: gcc -O3 -march=native -o theta.bin theta.c
   Usage: theta.bin NMAX p_1 ... p_K       prints "n theta(n) mod p_1 ... mod p_K", 19<=n<=NMAX
          (n <= 18 are taken from the enumeration and also printed, 9 <= n <= 18). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <sys/resource.h>

#define W 6
#define BASE 18
#define MAXN 2046      /* window entries are <= ceil(MAXN/2) and are packed in 10 bits */
#define MAXK 64
typedef unsigned __int128 u128;

static int K;
static uint64_t PR[MAXK], PINV[MAXK], R2[MAXK], ONE[MAXK];

static inline uint64_t redc(u128 t, int k) {
    uint64_t m = (uint64_t)t * PINV[k];
    u128 u = (t + (u128)m * PR[k]) >> 64;
    return u >= PR[k] ? (uint64_t)(u - PR[k]) : (uint64_t)u;
}
static inline uint64_t mmul(uint64_t a, uint64_t b, int k) { return redc((u128)a * b, k); }
static inline uint64_t madd(uint64_t a, uint64_t b, int k) { uint64_t s = a + b; return s >= PR[k] ? s - PR[k] : s; }
/* x mod p for x < p 2^64 (preserves the Montgomery form of a linear combination) */
static inline uint64_t mod128(u128 x, int k) { return mmul(redc(x, k), R2[k], k); }
static inline uint64_t mfrom(uint64_t x, int k) { return mmul(x % PR[k], R2[k], k); }
static inline uint64_t mto(uint64_t a, int k) { return redc(a, k); }
static void minit(void) {
    for (int k = 0; k < K; k++) {
        uint64_t p = PR[k], inv = p;
        for (int i = 0; i < 6; i++) inv *= 2 - p * inv;
        PINV[k] = -inv;
        u128 r = ((u128)1 << 64) % p;
        R2[k] = (uint64_t)((r * r) % p);
        ONE[k] = (uint64_t)r;
    }
}

/* ---------------- window sets and tries ---------------- */
static inline int getv(uint64_t key, int i) { return (int)((key >> (10 * (W - 1 - i))) & 1023); } /* i = 0..5 */
static uint64_t liftkey(uint64_t key, int p) {
    uint64_t r = 0;
    for (int i = 0; i < W; i++) r = (r << 10) | (uint64_t)(2 * getv(key, i) - p);
    return r;
}

typedef struct {
    int w;
    uint64_t *key;
    int *pos[2];            /* x >= 19: index in W_x of lift_0(W_floor[i]) / lift_1(W_ceil[i]) */
    int nn[W + 1];          /* trie nodes per depth; depth 0 = root, depth 6 = the windows */
    int *val[W + 1];        /* entry g_j of the node at depth j (1..6) */
    int *cs[W + 1];         /* children of node i at depth j: cs[j][i] .. cs[j][i+1]-1 at depth j+1 */
    uint64_t *t;            /* marginal (w x K), Montgomery */
    int have_t;
    /* base sizes: sparse J (CSR, symmetric), integer counts */
    int *jrow, *jcol; uint32_t *jval;
    uint64_t theta_small;
} Sz;
static Sz S[MAXN + 2];

static void build_trie(Sz *s) {
    int w = s->w;
    int *st = malloc(sizeof(int) * (w + 1)), *prevst = NULL; int pn = 0;
    s->nn[0] = 1;
    for (int j = 1; j <= W; j++) {
        int n = 0;
        for (int i = 0; i < w; i++)
            if (i == 0 || (s->key[i] >> (10 * (W - j))) != (s->key[i - 1] >> (10 * (W - j)))) st[n++] = i;
        s->nn[j] = n;
        s->val[j] = malloc(sizeof(int) * n);
        for (int i = 0; i < n; i++) s->val[j][i] = getv(s->key[st[i]], j - 1);
        /* children of depth j-1 nodes */
        s->cs[j - 1] = malloc(sizeof(int) * (s->nn[j - 1] + 1));
        if (j == 1) { s->cs[0][0] = 0; s->cs[0][1] = n; }
        else {
            int c = 0;
            for (int a = 0; a < pn; a++) {
                s->cs[j - 1][a] = c;
                int end = a + 1 < pn ? prevst[a + 1] : w;
                while (c < n && st[c] < end) c++;
            }
            s->cs[j - 1][pn] = n;
        }
        free(prevst); prevst = malloc(sizeof(int) * n); memcpy(prevst, st, sizeof(int) * n); pn = n;
    }
    free(prevst); free(st);
}

static int cmpu64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : x > y;
}
static int findk(const uint64_t *a, int n, uint64_t k) {
    int lo = 0, hi = n - 1;
    while (lo <= hi) { int mid = (lo + hi) / 2; if (a[mid] == k) return mid; if (a[mid] < k) lo = mid + 1; else hi = mid - 1; }
    return -1;
}

/* ---------------- base: enumerate Theta(m), 9 <= m <= 18 ---------------- */
static uint64_t *hk_, *gk_; static size_t nrec, caprec;
static int Kb, seqb[64], placedb[64], lenb;
static int okb(int v) {
    for (int t = 0; t < lenb; t++) { int y = 2 * v - seqb[t]; if (y >= 1 && y <= Kb && !placedb[y]) return 0; }
    return 1;
}
static void recb(void) {
    if (lenb == Kb) {
        uint64_t h = 0, g = 0;
        for (int i = 0; i < W; i++) { h = (h << 10) | seqb[i]; g = (g << 10) | seqb[Kb - 1 - i]; }
        if (nrec == caprec) { caprec = caprec ? 2 * caprec : 1024; hk_ = realloc(hk_, caprec * 8); gk_ = realloc(gk_, caprec * 8); }
        hk_[nrec] = h; gk_[nrec] = g; nrec++;
        return;
    }
    for (int v = 1; v <= Kb; v++) {
        if (placedb[v] || !okb(v)) continue;
        placedb[v] = 1; seqb[lenb++] = v; recb(); lenb--; placedb[v] = 0;
    }
}
typedef struct { int i, j; } IJ;
static int cmpij(const void *a, const void *b) {
    const IJ *x = a, *y = b; return x->i != y->i ? (x->i < y->i ? -1 : 1) : (x->j < y->j ? -1 : x->j > y->j);
}
static void base(int m) {
    Sz *s = &S[m];
    nrec = 0; Kb = m; lenb = 0; memset(placedb, 0, sizeof placedb); recb();
    uint64_t *ks = malloc(nrec * 8); memcpy(ks, hk_, nrec * 8);
    qsort(ks, nrec, 8, cmpu64);
    int w = 0; for (size_t i = 0; i < nrec; i++) if (!w || ks[w - 1] != ks[i]) ks[w++] = ks[i];
    s->w = w; s->key = ks; build_trie(s);
    IJ *e = malloc(sizeof(IJ) * nrec);
    for (size_t r = 0; r < nrec; r++) {
        e[r].i = findk(ks, w, hk_[r]); e[r].j = findk(ks, w, gk_[r]);
        if (e[r].i < 0 || e[r].j < 0) { fprintf(stderr, "base: reversed tail not a head (m=%d)\n", m); exit(1); }
    }
    qsort(e, nrec, sizeof(IJ), cmpij);
    s->jrow = calloc(w + 1, sizeof(int)); s->jcol = malloc(sizeof(int) * nrec); s->jval = malloc(4 * nrec);
    int nz = 0;
    for (size_t r = 0; r < nrec; r++) {
        if (r > 0 && e[r - 1].i == e[r].i && e[r - 1].j == e[r].j) { s->jval[nz - 1]++; continue; }
        s->jcol[nz] = e[r].j; s->jval[nz] = 1; s->jrow[e[r].i + 1]++; nz++;
    }
    for (int i = 1; i <= w; i++) s->jrow[i] += s->jrow[i - 1];
    free(e);
    s->t = malloc(8 * (size_t)w * K);
    for (int i = 0; i < w; i++) {
        uint64_t c = 0; for (int z = s->jrow[i]; z < s->jrow[i + 1]; z++) c += s->jval[z];
        for (int k = 0; k < K; k++) s->t[(size_t)i * K + k] = mfrom(c, k);
    }
    s->have_t = 1; s->theta_small = nrec;
}

/* W_x for x >= 19 by merging the two lifted halves */
static void build_W(int x) {
    Sz *s = &S[x], *A = &S[x / 2], *B = &S[(x + 1) / 2];
    int w = A->w + B->w, ia = 0, ib = 0, o = 0;
    s->w = w; s->key = malloc(8 * (size_t)w);
    s->pos[0] = malloc(sizeof(int) * A->w); s->pos[1] = malloc(sizeof(int) * B->w);
    while (ia < A->w || ib < B->w) {
        uint64_t ka = ia < A->w ? liftkey(A->key[ia], 0) : UINT64_MAX;
        uint64_t kb = ib < B->w ? liftkey(B->key[ib], 1) : UINT64_MAX;
        if (ka < kb) { s->key[o] = ka; s->pos[0][ia++] = o++; }
        else { s->key[o] = kb; s->pos[1][ib++] = o++; }
    }
    build_trie(s);
}

/* ---------------- the double-trie product  out = Pi_{N,q}^T a ---------------- */
static inline int linked(int N, int y, int u) {
    return (u < 2 * y && 2 * y <= N + u) || (y < 2 * u && 2 * u <= N + y);
}
typedef struct {
    int N, q;
    Sz *D, *C;
    uint64_t *Us[W + 1];     /* subtree sums of the row weights, per S-depth */
    u128 *Acc[W + 1];        /* accumulators per T-depth */
    int ys[W + 1], us[W + 1];
    long long leaves;
} Ctx;

static int pi_small(Ctx *c, int I, int Kc) {
    if (I == 0 || Kc == 0) return 1;
    int r[W + 1], cur = Kc;
    for (int i = 1; i <= I; i++) {
        for (int k = 1; k <= cur; k++) if (linked(c->N, c->ys[k], c->us[i])) { cur = k - 1; break; }
        r[i] = cur;
    }
    int f[W + 1];
    for (int v = 0; v <= W; v++) f[v] = v <= r[1];
    for (int i = 2; i <= I; i++) {
        int acc = 0;
        for (int v = W; v >= 0; v--) { acc += f[v]; f[v] = v <= r[i] ? acc : 0; }
    }
    int P = 0; for (int v = 0; v <= W; v++) P += f[v];
    return P;
}
static inline void leaf(Ctx *c, int a, int sn, int b, int tn, int i0, int k0) {
    int P = pi_small(c, i0 ? i0 - 1 : W, k0 ? k0 - 1 : W);
    const uint64_t *u = c->Us[a] + (size_t)sn * K;
    u128 *acc = c->Acc[b] + (size_t)tn * K;
    for (int k = 0; k < K; k++) acc[k] += (u128)P * u[k];
    c->leaves++;
}
/* S phase: T fixed at (b, tn) with closure i0 */
static void phaseS(Ctx *c, int a, int sn, int k0, int b, int tn, int i0) {
    if (k0 || a == W) { leaf(c, a, sn, b, tn, i0, k0); return; }
    Sz *D = c->D; int u1 = c->us[1];
    for (int s = D->cs[a][sn]; s < D->cs[a][sn + 1]; s++) {
        int y = 2 * D->val[a + 1][s] - c->q; c->ys[a + 1] = y;
        phaseS(c, a + 1, s, linked(c->N, y, u1) ? a + 1 : 0, b, tn, i0);
    }
}
/* T phase: S at depth 1 (node sn) */
static void phaseT(Ctx *c, int sn, int b, int tn, int i0, int k0) {
    if (i0 || b == W) { phaseS(c, 1, sn, k0, b, tn, i0); return; }
    Sz *C = c->C; int y1 = c->ys[1];
    for (int t = C->cs[b][tn]; t < C->cs[b][tn + 1]; t++) {
        int u = 2 * C->val[b + 1][t] - (1 - c->q); c->us[b + 1] = u;
        phaseT(c, sn, b + 1, t, linked(c->N, y1, u) ? b + 1 : 0, k0);
    }
}
static long long total_leaves;
/* out (over W_c, K residues) = Pi_{N,q}^T a,  a over W_d */
static void pi_apply(int N, int q, int d, int cc, const uint64_t *a, uint64_t *out) {
    Ctx c; c.N = N; c.q = q; c.D = &S[d]; c.C = &S[cc]; c.leaves = 0;
    Sz *D = c.D, *C = c.C;
    /* subtree sums */
    c.Us[W] = (uint64_t *)a;
    for (int j = W - 1; j >= 1; j--) {
        c.Us[j] = malloc(8 * (size_t)D->nn[j] * K);
        for (int i = 0; i < D->nn[j]; i++) {
            uint64_t *o = c.Us[j] + (size_t)i * K;
            for (int k = 0; k < K; k++) o[k] = 0;
            for (int ch = D->cs[j][i]; ch < D->cs[j][i + 1]; ch++) {
                const uint64_t *x = c.Us[j + 1] + (size_t)ch * K;
                for (int k = 0; k < K; k++) o[k] = madd(o[k], x[k], k);
            }
        }
    }
    for (int j = 1; j <= W; j++) c.Acc[j] = calloc((size_t)C->nn[j] * K, sizeof(u128));
    for (int s = 0; s < D->nn[1]; s++) {
        int y1 = 2 * D->val[1][s] - q; c.ys[1] = y1;
        for (int t = 0; t < C->nn[1]; t++) {
            int u1 = 2 * C->val[1][t] - (1 - q); c.us[1] = u1;
            int l = linked(N, y1, u1);
            phaseT(&c, s, 1, t, l, l);
        }
    }
    /* push down */
    uint64_t *prev = NULL;
    for (int j = 1; j <= W; j++) {
        uint64_t *cur = (j == W) ? out : malloc(8 * (size_t)C->nn[j] * K);
        for (int i = 0; i < C->nn[j]; i++)
            for (int k = 0; k < K; k++) cur[(size_t)i * K + k] = mod128(c.Acc[j][(size_t)i * K + k], k);
        if (prev)
            for (int i = 0; i < C->nn[j - 1]; i++)
                for (int ch = C->cs[j - 1][i]; ch < C->cs[j - 1][i + 1]; ch++)
                    for (int k = 0; k < K; k++) cur[(size_t)ch * K + k] = madd(cur[(size_t)ch * K + k], prev[(size_t)i * K + k], k);
        free(prev); prev = (j == W) ? NULL : cur;
        free(c.Acc[j]);
    }
    for (int j = 1; j < W; j++) free(c.Us[j]);
    total_leaves += c.leaves;
}

/* ---------------- L_x(v) = J_x v ---------------- */
static void Lx(int x, const uint64_t *v, uint64_t *out) {
    Sz *s = &S[x];
    if (x <= BASE) {
        for (int i = 0; i < s->w; i++) {
            u128 acc[MAXK]; for (int k = 0; k < K; k++) acc[k] = 0;
            for (int z = s->jrow[i]; z < s->jrow[i + 1]; z++) {
                const uint64_t *vv = v + (size_t)s->jcol[z] * K; uint64_t m = s->jval[z];
                for (int k = 0; k < K; k++) acc[k] += (u128)m * vv[k];
            }
            for (int k = 0; k < K; k++) out[(size_t)i * K + k] = mod128(acc[k], k);
        }
        return;
    }
    for (int q = 0; q < 2; q++) {
        int d = (x + q) / 2, c = (x + 1 - q) / 2;
        int wd = S[d].w, wc = S[c].w;
        uint64_t *vq = malloc(8 * (size_t)wd * K), *a = malloc(8 * (size_t)wd * K);
        uint64_t *b = malloc(8 * (size_t)wc * K), *cv = malloc(8 * (size_t)wc * K);
        const int *pin = s->pos[q];          /* lift_q(W_d) : q=0 -> floor half (pos[0]), q=1 -> ceil (pos[1]) */
        for (int i = 0; i < wd; i++) memcpy(vq + (size_t)i * K, v + (size_t)pin[i] * K, 8 * K);
        Lx(d, vq, a);
        pi_apply(x, q, d, c, a, b);
        Lx(c, b, cv);
        const int *pout = s->pos[1 - q];     /* lift_{1-q}(W_c) */
        for (int i = 0; i < wc; i++) memcpy(out + (size_t)pout[i] * K, cv + (size_t)i * K, 8 * K);
        free(vq); free(a); free(b); free(cv);
    }
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s NMAX p1 [p2 ...]\n", argv[0]); return 1; }
    int NMAX = atoi(argv[1]);
    K = argc - 2;
    if (K > MAXK || NMAX > MAXN) { fprintf(stderr, "too many primes / NMAX too large\n"); return 1; }
    for (int k = 0; k < K; k++) {
        PR[k] = strtoull(argv[2 + k], NULL, 10);
        if (PR[k] >= (1ULL << 61) || PR[k] % 2 == 0) { fprintf(stderr, "primes must be odd and < 2^61\n"); return 1; }
    }
    minit();
    int half = (NMAX + 1) / 2;            /* marginals needed for sizes <= half */
    clock_t t0 = clock();
    printf("#");
    for (int k = 0; k < K; k++) printf(" %llu", (unsigned long long)PR[k]);
    printf("\n");
    for (int m = 9; m <= BASE; m++) {
        base(m);
        printf("%d", m);
        for (int k = 0; k < K; k++) printf(" %llu", (unsigned long long)(S[m].theta_small % PR[k]));
        printf("\n");
    }
    uint64_t *tmp = NULL;
    for (int x = 19; x <= NMAX; x++) {
        int needW = x <= half;
        if (needW) build_W(x);
        uint64_t th[MAXK]; for (int k = 0; k < K; k++) th[k] = 0;
        if (needW) S[x].t = malloc(8 * (size_t)S[x].w * K);
        for (int q = 0; q < 2; q++) {
            int d = (x + q) / 2, c = (x + 1 - q) / 2, wc = S[c].w;
            uint64_t *b = malloc(8 * (size_t)wc * K);
            pi_apply(x, q, d, c, S[d].t, b);
            for (int i = 0; i < wc; i++) for (int k = 0; k < K; k++)
                th[k] = madd(th[k], mmul(b[(size_t)i * K + k], S[c].t[(size_t)i * K + k], k), k);
            if (needW) {
                tmp = malloc(8 * (size_t)wc * K);
                Lx(c, b, tmp);
                const int *pout = S[x].pos[1 - q];
                for (int i = 0; i < wc; i++) memcpy(S[x].t + (size_t)pout[i] * K, tmp + (size_t)i * K, 8 * K);
                free(tmp);
            }
            free(b);
        }
        if (needW) S[x].have_t = 1;
        /* t_y is used only by the sizes 2y-1, 2y, 2y+1 */
        for (int y = 9; 2 * y + 1 <= x; y++) if (S[y].t) { free(S[y].t); S[y].t = NULL; S[y].have_t = 0; }
        printf("%d", x);
        for (int k = 0; k < K; k++) printf(" %llu", (unsigned long long)mto(th[k], k));
        printf("\n"); fflush(stdout);
        struct rusage ru; getrusage(RUSAGE_SELF, &ru);
        fprintf(stderr, "n=%d w=%d leaves=%lld cpu=%.1fs maxrss=%ldMB\n", x, needW ? S[x].w : -1,
                total_leaves, (double)(clock() - t0) / CLOCKS_PER_SEC, ru.ru_maxrss / 1024);
    }
    return 0;
}

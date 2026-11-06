/* window.c -- exact computation of theta(n) = A003407(n) and r(n) by the WINDOW RECURSION
   (experiments/symratio/PROOFS.txt, Theorems W and J).

   For a 3-AP-free permutation a of [m] let head(a) = first 6 entries, tail(a) = last 6.
   J_m(H,T) = #{a : head H, tail T}.  For m >= 19 (where the opening and closing runs have
   length >= 6) and parity p (D = class p of size d = (m+p)/2, C = the other, c = (m+1-p)/2):
       J_m(lift_p H, lift_{1-p} T) = sum_{T', H'} J_d(H, T') Pi_{m,p}(T', H') J_c(H', T)
   where Pi_{m,p}(T', H') = number of interleavings of lift_p(T') and lift_{1-p}(H') in which
   every linked pair (y in D, u in C) has y first (Theorem W: P(sigma,tau) = Pi(window)).
   Hence theta(m) = sum_p sum t_d(T') Pi h_c(H') with t, h the tail / head marginals, and
   r(m) = theta(m)/(2 theta(floor m/2) theta(ceil m/2)) = (E_0 + E_1)/2,
   E_p = E[Pi_{m,p}] for independent uniform sigma in Theta(d), tau in Theta(c).

   Build: gcc -O3 -march=native -o window.bin window.c -lm          (double, normalised)
          gcc -O3 -march=native -DMODP -o window_mod.bin window.c -lm   (exact mod 2^61-1,
          or mod the prime in the environment variable PRIME, < 2^62)
   Usage: window.bin all NMAX          r(n) for 19 <= n <= NMAX
          window.bin chain n1 n2 ...   r(n) for the listed n only
          window.bin stats NMAX        also head-tail correlation and state counts
   Output lines: "n r(n) log(theta(n)) nh nt maxPi Pr(Pi=1) Pr(tie) [corr]"
   (nh, nt = numbers of head / tail windows of Theta(n); maxPi = max of Pi over the window
   pairs that occur; Pr(tie) = probability that some 3-AP through a window pair has its
   third term at 0 or n+1, the only pairs whose linkage changes under lifting; corr (stats mode) = total variation between J_n and the product of its
   marginals).  Mod build: "n theta(n) mod PRIME".
   Uses one core; memory ~ 84 * (NMAX/4)^3 doubles in "all" mode. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define W 6
#define BASE 18          /* sizes <= BASE are enumerated directly */
#define MAXN 4200

#ifdef MODP
typedef uint64_t num;
/* Montgomery arithmetic modulo an odd prime PR < 2^62 (default 2^61-1; override with the
   environment variable PRIME).  Values are stored as x*2^64 mod PR. */
static uint64_t PR = (1ULL << 61) - 1, PINV, R2;
static inline num nadd(num a, num b) { num s = a + b; return s >= PR ? s - PR : s; }
static inline uint64_t redc(unsigned __int128 t) {
    uint64_t m = (uint64_t)t * PINV;
    unsigned __int128 u = (t + (unsigned __int128)m * PR) >> 64;
    return u >= PR ? (uint64_t)(u - PR) : (uint64_t)u;
}
static inline num nmul(num a, num b) { return redc((unsigned __int128)a * b); }
static inline num nfrom(uint64_t x) { return redc((unsigned __int128)(x % PR) * R2); }
static uint64_t nto(num a) { return redc(a); }
static void minit(void) {
    uint64_t inv = PR;                       /* Newton: inv = PR^-1 mod 2^64 */
    for (int i = 0; i < 6; i++) inv *= 2 - PR * inv;
    PINV = -inv;
    unsigned __int128 r = ((unsigned __int128)1 << 64) % PR;
    R2 = (uint64_t)((r * r) % PR);
}
#else
typedef double num;
static inline num nadd(num a, num b) { return a + b; }
static inline num nmul(num a, num b) { return a * b; }
static inline num nfrom(uint64_t x) { return (double)x; }
#endif

typedef struct {
    int have;                 /* 0 none, 1 marginals, 2 marginals + J */
    int nh[2], nt[2];         /* block q = parity of the first entry */
    uint64_t *hk[2], *tk[2];  /* packed windows (10 bits per value, index 0 = first) */
    num *J[2];                /* nh[q] x nt[q] */
    num *th[2], *hh[2];       /* tail / head marginals */
    long double logth;        /* log theta(m) */
    double r;
    int maxpi;                /* max of Pi over window pairs in the support (both p) */
    double p1;                /* probability (averaged over p) that Pi = 1 */
    double tie;               /* probability (averaged over p) of a boundary tie */
    num tot;                  /* MODP: theta(m) mod p */
} Size;

static Size S[MAXN + 2];
static int need[MAXN + 2], lastuse[MAXN + 2];

static inline int getv(uint64_t k, int i) { return (int)((k >> (10 * i)) & 1023); }
static uint64_t liftkey(uint64_t k, int p) {
    uint64_t r = 0;
    for (int i = 0; i < W; i++) r |= (uint64_t)(2 * getv(k, i) - p) << (10 * i);
    return r;
}
static inline int linked(int N, int y, int u) {
    return (u < 2 * y && 2 * y <= N + u) || (y < 2 * u && 2 * u <= N + y);
}

/* Pi: the number of interleavings of Y[0..5] (D, in order) and U[0..5] (C, in order) with
   y before u on every linked pair.  c_j = #Y before U_j, nondecreasing, c_j >= M_j. */
/* a boundary tie: some 3-AP through a window pair has its third term at 0 or N+1 */
static int tie(int N, const int *Y, const int *U) {
    for (int i = 0; i < W; i++) for (int j = 0; j < W; j++) {
        int a = 2 * Y[i] - U[j], b = 2 * U[j] - Y[i];
        if (a == 0 || a == N + 1 || b == 0 || b == N + 1) return 1;
    }
    return 0;
}
static int piv(int N, const int *Y, const int *U) {
    int M = 0, ways[W + 1], nw[W + 1];
    for (int c = 0; c <= W; c++) ways[c] = (c == 0);
    for (int j = 0; j < W; j++) {
        for (int i = W; i >= 1; i--) if (linked(N, Y[i - 1], U[j])) { if (i > M) M = i; break; }
        int acc = 0;
        for (int c = 0; c <= W; c++) { acc += ways[c]; nw[c] = c >= M ? acc : 0; }
        memcpy(ways, nw, sizeof ways);
    }
    int P = 0; for (int c = 0; c <= W; c++) P += ways[c];
    return P;
}

/* ---------------- base: enumerate Theta(m) ---------------- */
typedef struct { int q; uint64_t h, t; } Rec;
static Rec *recs; static size_t nrec, caprec;
static int Kb, seqb[64], placedb[64], lenb;
static int okb(int v) {
    for (int t = 0; t < lenb; t++) { int y = 2 * v - seqb[t]; if (y >= 1 && y <= Kb && !placedb[y]) return 0; }
    return 1;
}
static void recb(void) {
    if (lenb == Kb) {
        uint64_t h = 0, t = 0;
        for (int i = 0; i < W; i++) { h |= (uint64_t)seqb[i] << (10 * i); t |= (uint64_t)seqb[Kb - W + i] << (10 * i); }
        if (nrec == caprec) { caprec = caprec ? 2 * caprec : 1024; recs = realloc(recs, caprec * sizeof(Rec)); }
        recs[nrec].q = seqb[0] % 2; recs[nrec].h = h; recs[nrec].t = t; nrec++;
        return;
    }
    for (int v = 1; v <= Kb; v++) {
        if (placedb[v] || !okb(v)) continue;
        placedb[v] = 1; seqb[lenb++] = v; recb(); lenb--; placedb[v] = 0;
    }
}
static int cmpu64(const void *a, const void *b) {
    uint64_t x = *(const uint64_t *)a, y = *(const uint64_t *)b; return x < y ? -1 : x > y;
}
static int findk(const uint64_t *a, int n, uint64_t k) {
    int lo = 0, hi = n - 1;
    while (lo <= hi) { int mid = (lo + hi) / 2; if (a[mid] == k) return mid; if (a[mid] < k) lo = mid + 1; else hi = mid - 1; }
    return -1;
}
static void base(int m) {
    Size *s = &S[m];
    nrec = 0; Kb = m; lenb = 0; memset(placedb, 0, sizeof placedb); recb();
    for (int q = 0; q < 2; q++) {
        uint64_t *hs = malloc(nrec * 8), *ts = malloc(nrec * 8); int a = 0;
        for (size_t i = 0; i < nrec; i++) if (recs[i].q == q) { hs[a] = recs[i].h; ts[a] = recs[i].t; a++; }
        qsort(hs, a, 8, cmpu64); qsort(ts, a, 8, cmpu64);
        int nh = 0, nt = 0;
        for (int i = 0; i < a; i++) { if (!nh || hs[nh - 1] != hs[i]) hs[nh++] = hs[i]; }
        for (int i = 0; i < a; i++) { if (!nt || ts[nt - 1] != ts[i]) ts[nt++] = ts[i]; }
        s->nh[q] = nh; s->nt[q] = nt; s->hk[q] = hs; s->tk[q] = ts;
        s->J[q] = calloc((size_t)nh * nt, sizeof(num));
        s->th[q] = calloc(nt, sizeof(num)); s->hh[q] = calloc(nh, sizeof(num));
    }
    for (size_t i = 0; i < nrec; i++) {
        int q = recs[i].q;
        int hi = findk(S[m].hk[q], s->nh[q], recs[i].h), ti = findk(s->tk[q], s->nt[q], recs[i].t);
        s->J[q][(size_t)hi * s->nt[q] + ti] = nadd(s->J[q][(size_t)hi * s->nt[q] + ti], nfrom(1));
    }
#ifndef MODP
    double inv = 1.0 / (double)nrec;
#endif
    for (int q = 0; q < 2; q++) for (int i = 0; i < s->nh[q]; i++) for (int j = 0; j < s->nt[q]; j++) {
        num *e = &s->J[q][(size_t)i * s->nt[q] + j];
#ifndef MODP
        *e *= inv;
#endif
        s->hh[q][i] = nadd(s->hh[q][i], *e); s->th[q][j] = nadd(s->th[q][j], *e);
    }
    s->logth = logl((long double)nrec); s->tot = nfrom(nrec); s->r = 0; s->have = 2;
}

/* ---------------- recursion ---------------- */
static void freeJ(int m) {
    for (int q = 0; q < 2; q++) { free(S[m].J[q]); S[m].J[q] = NULL; }
    if (S[m].have == 2) S[m].have = 1;
}

static void compute(int m, int level) {
    Size *s = &S[m];
    num E[2]; num *Jb[2] = {0, 0}, *thb[2] = {0, 0}, *hhb[2] = {0, 0};
    int nhp[2], ntp[2]; uint64_t *hkp[2], *tkp[2];
    s->maxpi = 0; s->p1 = 0; s->tie = 0;
    for (int p = 0; p < 2; p++) {
        int d = (m + p) / 2, c = (m + 1 - p) / 2;
        Size *D = &S[d], *Cc = &S[c];
        int ntD = D->nt[0] + D->nt[1], nhD = D->nh[0] + D->nh[1];
        int nhC = Cc->nh[0] + Cc->nh[1], ntC = Cc->nt[0] + Cc->nt[1];
        /* lifted windows */
        int (*Y)[W] = malloc(sizeof(int[W]) * ntD), (*U)[W] = malloc(sizeof(int[W]) * nhC);
        for (int q = 0, o = 0; q < 2; q++) for (int i = 0; i < D->nt[q]; i++, o++)
            for (int k = 0; k < W; k++) Y[o][k] = 2 * getv(D->tk[q][i], k) - p;
        for (int q = 0, o = 0; q < 2; q++) for (int i = 0; i < Cc->nh[q]; i++, o++)
            for (int k = 0; k < W; k++) U[o][k] = 2 * getv(Cc->hk[q][i], k) - (1 - p);
        /* marginal vectors of the children */
        num *tD = malloc(sizeof(num) * ntD), *hC = malloc(sizeof(num) * nhC);
        memcpy(tD, D->th[0], sizeof(num) * D->nt[0]); memcpy(tD + D->nt[0], D->th[1], sizeof(num) * D->nt[1]);
        memcpy(hC, Cc->hh[0], sizeof(num) * Cc->nh[0]); memcpy(hC + Cc->nh[0], Cc->hh[1], sizeof(num) * Cc->nh[1]);
        /* Pi row by row (stored only when J is wanted); v = t_D Pi, w = Pi h_C */
        num *Pi = level >= 2 ? malloc(sizeof(num) * (size_t)ntD * nhC) : NULL;
        num *row = malloc(sizeof(num) * nhC);
        num *v = calloc(nhC, sizeof(num)), *w = calloc(ntD, sizeof(num));
        double one = 0, tt = 0;
        for (int i = 0; i < ntD; i++) {
            num *pr = Pi ? Pi + (size_t)i * nhC : row;
            num acc = 0;
            for (int j = 0; j < nhC; j++) {
                int pv = piv(m, Y[i], U[j]);
                if (pv > s->maxpi) s->maxpi = pv;
                num x = nfrom(pv); pr[j] = x;
                v[j] = nadd(v[j], nmul(tD[i], x)); acc = nadd(acc, nmul(x, hC[j]));
#ifndef MODP
                if (pv == 1) one += tD[i] * hC[j];
                if (tie(m, Y[i], U[j])) tt += tD[i] * hC[j];
#endif
            }
            w[i] = acc;
        }
        free(row); free(Y);
        E[p] = 0; for (int j = 0; j < nhC; j++) E[p] = nadd(E[p], nmul(v[j], hC[j]));
#ifndef MODP
        { double tsum = 0, hsum = 0;
          for (int i = 0; i < ntD; i++) tsum += tD[i];
          for (int j = 0; j < nhC; j++) hsum += hC[j];
          s->p1 += one / (tsum * hsum) / 2; s->tie += tt / (tsum * hsum) / 2; }
#endif
        nhp[p] = nhD; ntp[p] = ntC;
        hkp[p] = malloc(8 * (size_t)nhD); tkp[p] = malloc(8 * (size_t)ntC);
        for (int q = 0, o = 0; q < 2; q++) for (int i = 0; i < D->nh[q]; i++) hkp[p][o++] = liftkey(D->hk[q][i], p);
        for (int q = 0, o = 0; q < 2; q++) for (int i = 0; i < Cc->nt[q]; i++) tkp[p][o++] = liftkey(Cc->tk[q][i], 1 - p);
        if (level >= 1) {
            /* tail marginal: v * blockdiag(J_C);  head marginal: blockdiag(J_D) * w */
            thb[p] = calloc(ntC, sizeof(num)); hhb[p] = calloc(nhD, sizeof(num));
            for (int q = 0, oh = 0, ot = 0; q < 2; oh += Cc->nh[q], ot += Cc->nt[q], q++)
                for (int i = 0; i < Cc->nh[q]; i++) {
                    num a = v[oh + i]; const num *row = Cc->J[q] + (size_t)i * Cc->nt[q];
                    for (int j = 0; j < Cc->nt[q]; j++) thb[p][ot + j] = nadd(thb[p][ot + j], nmul(a, row[j]));
                }
            for (int q = 0, oh = 0, ot = 0; q < 2; oh += D->nh[q], ot += D->nt[q], q++)
                for (int i = 0; i < D->nh[q]; i++) {
                    const num *row = D->J[q] + (size_t)i * D->nt[q]; num acc = 0;
                    for (int j = 0; j < D->nt[q]; j++) acc = nadd(acc, nmul(row[j], w[ot + j]));
                    hhb[p][oh + i] = acc;
                }
        }
        if (level >= 2) {
            /* X = blockdiag(J_D) Pi  (nhD x nhC),  J = X blockdiag(J_C)  (nhD x ntC) */
            num *X = calloc((size_t)nhD * nhC, sizeof(num));
            for (int q = 0, oh = 0, ot = 0; q < 2; oh += D->nh[q], ot += D->nt[q], q++)
                for (int i = 0; i < D->nh[q]; i++) {
                    num *xr = X + (size_t)(oh + i) * nhC; const num *ar = D->J[q] + (size_t)i * D->nt[q];
                    for (int k = 0; k < D->nt[q]; k++) {
                        num a = ar[k]; if (a == 0) continue;
                        const num *pr = Pi + (size_t)(ot + k) * nhC;
                        for (int j = 0; j < nhC; j++) xr[j] = nadd(xr[j], nmul(a, pr[j]));
                    }
                }
            Jb[p] = calloc((size_t)nhD * ntC, sizeof(num));
            for (int i = 0; i < nhD; i++) {
                num *jr = Jb[p] + (size_t)i * ntC; const num *xr = X + (size_t)i * nhC;
                for (int q = 0, oh = 0, ot = 0; q < 2; oh += Cc->nh[q], ot += Cc->nt[q], q++)
                    for (int k = 0; k < Cc->nh[q]; k++) {
                        num a = xr[oh + k]; if (a == 0) continue;
                        const num *br = Cc->J[q] + (size_t)k * Cc->nt[q];
                        for (int j = 0; j < Cc->nt[q]; j++) jr[ot + j] = nadd(jr[ot + j], nmul(a, br[j]));
                    }
            }
            free(X);
        }
        free(Pi); free(tD); free(hC); free(v); free(w); free(U);
    }
    num tot = nadd(E[0], E[1]);
    int h0 = m / 2, h1 = (m + 1) / 2;
    s->logth = S[h0].logth + S[h1].logth + logl((long double)tot);
#ifdef MODP
    s->tot = tot;  /* children are raw counts */
    s->r = 0;
#else
    s->r = tot / 2; s->tot = 1;
    double inv = 1.0 / tot;
    for (int p = 0; p < 2; p++) {
        if (thb[p]) for (int j = 0; j < ntp[p]; j++) thb[p][j] *= inv;
        if (hhb[p]) for (int j = 0; j < nhp[p]; j++) hhb[p][j] *= inv;
        if (Jb[p]) for (size_t j = 0; j < (size_t)nhp[p] * ntp[p]; j++) Jb[p][j] *= inv;
    }
#endif
    for (int p = 0; p < 2; p++) {
        s->nh[p] = nhp[p]; s->nt[p] = ntp[p]; s->hk[p] = hkp[p]; s->tk[p] = tkp[p];
        s->J[p] = Jb[p]; s->th[p] = thb[p]; s->hh[p] = hhb[p];
    }
    s->have = level >= 2 ? 2 : 1;
}

#ifndef MODP
/* total-variation distance between J_m and the product of its marginals */
static double corr(int m) {
    Size *s = &S[m]; double tv = 0;
    for (int q = 0; q < 2; q++) {
        double mass = 0; for (int i = 0; i < s->nh[q]; i++) mass += s->hh[q][i];
        for (int i = 0; i < s->nh[q]; i++) for (int j = 0; j < s->nt[q]; j++)
            tv += fabs(s->J[q][(size_t)i * s->nt[q] + j] - s->hh[q][i] * s->th[q][j] / mass);
    }
    return tv / 2;
}
#endif

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s all NMAX | chain n... | stats NMAX\n", argv[0]); return 1; }
#ifdef MODP
    if (getenv("PRIME")) PR = strtoull(getenv("PRIME"), NULL, 10);
    minit();
#endif
    int stats = !strcmp(argv[1], "stats");
    int top = 0;
    for (int i = 0; i <= MAXN; i++) need[i] = -1;
    if (!strcmp(argv[1], "all") || stats) {
        top = atoi(argv[2]);
        for (int n = 19; n <= top; n++) need[n] = stats ? 2 : 0;
    } else {
        for (int i = 2; i < argc; i++) { int n = atoi(argv[i]); if (n > top) top = n; need[n] = 0; }
    }
    if (top > MAXN) { fprintf(stderr, "n too large\n"); return 1; }
    for (int m = top; m >= 19; m--) if (need[m] >= 0) {
        int lv = need[m] >= 1 ? 2 : 1;
        for (int c = m / 2; c <= (m + 1) / 2; c++) if (need[c] < lv) need[c] = lv;
    }
    for (int m = 0; m <= top; m++) lastuse[m] = -1;
    for (int m = 19; m <= top; m++) if (need[m] >= 1) { lastuse[m / 2] = m; lastuse[(m + 1) / 2] = m; }
    for (int m = 9; m <= top; m++) {
        if (need[m] < 0) continue;
        if (m <= BASE) base(m); else compute(m, need[m]);
        if (m >= 19 && (need[m] == 0 || !strcmp(argv[1], "chain") || stats || 1)) {
#ifdef MODP
            printf("%d %llu\n", m, (unsigned long long)nto(S[m].tot));
#else
            int nh = S[m].nh[0] + S[m].nh[1], nt = S[m].nt[0] + S[m].nt[1];
            printf("%d %.12f %.10Lf %d %d %d %.6f %.3e", m, S[m].r, S[m].logth, nh, nt,
                   S[m].maxpi, S[m].p1, S[m].tie);
            if (stats && S[m].have == 2) printf(" %.3e", corr(m));
            printf("\n");
#endif
            fflush(stdout);
        }
        for (int x = 9; x < m; x++) if (S[x].have == 2 && lastuse[x] == m && !(stats && x <= top)) freeJ(x);
        if (S[m].have == 2 && lastuse[m] < 0 && !stats) freeJ(m);
    }
    return 0;
}

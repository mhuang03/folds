/* pilib.c -- helpers for experiments/symratio2 (called from Python via ctypes).
   enum_base(m, heads, tails, cap): enumerate Theta(m) (3-AP-free perms of [1,m]); write
     head (first 6) and reversed tail (last 6, last entry first) of each, 6 ints each.
   pi_dense(N, q, nD, Dwin, nC, Cwin, out): out[s*nC+t] = Pi_{N,q}(S_s, T_t) of Theorem W,
     S_s = reversed tail (lifted by q: y'_k = 2 S_s[k-1] - q), T_t = head (lifted by 1-q:
     u_i = 2 T_t[i-1] - (1-q)); Pi = # Young diagrams in the 6x6 box avoiding linked cells.
   Build: gcc -O3 -march=native -shared -fPIC -o pilib.so pilib.c */
#include <stdint.h>
#include <string.h>
#define W 6
static int Kb, seqb[64], placedb[64], lenb; static long nrec, capb; static int *H_, *T_;
static int okb(int v) {
    for (int t = 0; t < lenb; t++) { int y = 2 * v - seqb[t]; if (y >= 1 && y <= Kb && !placedb[y]) return 0; }
    return 1;
}
static void recb(void) {
    if (lenb == Kb) {
        if (nrec < capb) for (int i = 0; i < W; i++) { H_[nrec * W + i] = seqb[i]; T_[nrec * W + i] = seqb[Kb - 1 - i]; }
        nrec++; return;
    }
    for (int v = 1; v <= Kb; v++) {
        if (placedb[v] || !okb(v)) continue;
        placedb[v] = 1; seqb[lenb++] = v; recb(); lenb--; placedb[v] = 0;
    }
}
long enum_base(int m, int *heads, int *tails, long cap) {
    Kb = m; lenb = 0; nrec = 0; capb = cap; H_ = heads; T_ = tails; memset(placedb, 0, sizeof placedb);
    recb(); return nrec;
}
static inline int linked(int N, int y, int u) {
    return (u < 2 * y && 2 * y <= N + u) || (y < 2 * u && 2 * u <= N + y);
}
int pi_one(int N, const int *ys, const int *us) {   /* ys[0..5] = y'_1..y'_6, us = u_1..u_6 */
    int r[W + 1], cur = W;
    for (int i = 1; i <= W; i++) {
        for (int k = 1; k <= cur; k++) if (linked(N, ys[k - 1], us[i - 1])) { cur = k - 1; break; }
        r[i] = cur;
    }
    int f[W + 1];
    for (int v = 0; v <= W; v++) f[v] = v <= r[1];
    for (int i = 2; i <= W; i++) {
        int acc = 0;
        for (int v = W; v >= 0; v--) { acc += f[v]; f[v] = v <= r[i] ? acc : 0; }
    }
    int P = 0; for (int v = 0; v <= W; v++) P += f[v];
    return P;
}
/* shifted linkage at size L: 1+g <= 2y-u <= L+g  or  1+h <= 2u-y <= L+h  (g = h = 0: linked) */
static inline int linked_gh(int L, int g, int h, int y, int u) {
    int A = 2 * y - u, B = 2 * u - y;
    return (A >= 1 + g && A <= L + g) || (B >= 1 + h && B <= L + h);
}
int pi_one_gh(int L, int g, int h, const int *ys, const int *us) {
    int r[W + 1], cur = W;
    for (int i = 1; i <= W; i++) {
        for (int k = 1; k <= cur; k++) if (linked_gh(L, g, h, ys[k - 1], us[i - 1])) { cur = k - 1; break; }
        r[i] = cur;
    }
    int f[W + 1];
    for (int v = 0; v <= W; v++) f[v] = v <= r[1];
    for (int i = 2; i <= W; i++) {
        int acc = 0;
        for (int v = W; v >= 0; v--) { acc += f[v]; f[v] = v <= r[i] ? acc : 0; }
    }
    int P = 0; for (int v = 0; v <= W; v++) P += f[v];
    return P;
}
/* out[(s*nC+t)*9 + 3*(g+1)+(h+1)] = Pi^{(g,h)}_L(S_s, T_t), raw (unlifted) windows, g,h in {-1,0,1} */
void pi_gh_all(int L, int nD, const int *Dwin, int nC, const int *Cwin, int *out) {
    for (int s = 0; s < nD; s++)
        for (int t = 0; t < nC; t++)
            for (int g = -1; g <= 1; g++)
                for (int h = -1; h <= 1; h++)
                    out[((long)s * nC + t) * 9 + 3 * (g + 1) + (h + 1)] = pi_one_gh(L, g, h, Dwin + s * W, Cwin + t * W);
}
/* outT = Pi^T a (length nC), outN = Pi b (length nD), Pi = Pi_{N,q}(D rows, C cols), no storage */
void pi_mv(int N, int q, int nD, const int *Dwin, int nC, const int *Cwin,
           const double *a, const double *b, double *outT, double *outN) {
    int ys[W], us[W];
    for (int t = 0; t < nC; t++) outT[t] = 0;
    for (int s = 0; s < nD; s++) {
        for (int k = 0; k < W; k++) ys[k] = 2 * Dwin[s * W + k] - q;
        double acc = 0, as = a[s];
        for (int t = 0; t < nC; t++) {
            for (int i = 0; i < W; i++) us[i] = 2 * Cwin[t * W + i] - (1 - q);
            int P = pi_one(N, ys, us);
            acc += P * b[t];
            outT[t] += P * as;
        }
        outN[s] = acc;
    }
}
void pi_dense(int N, int q, int nD, const int *Dwin, int nC, const int *Cwin, double *out) {
    int ys[W], us[W];
    for (int s = 0; s < nD; s++) {
        for (int k = 0; k < W; k++) ys[k] = 2 * Dwin[s * W + k] - q;
        for (int t = 0; t < nC; t++) {
            for (int i = 0; i < W; i++) us[i] = 2 * Cwin[t * W + i] - (1 - q);
            out[(long)s * nC + t] = pi_one(N, ys, us);
        }
    }
}

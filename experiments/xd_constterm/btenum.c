// Enumerate all balanced tournaments on [N] (N <= 9) and classify them:
//   B        all balanced tournaments
//   T3       balanced tournaments without a 3-cycle (= transitive = a(N))
//   Wtr      balanced, and for every m the sub-tournament on W(m) + {m} is transitive
//   Loc      balanced, and for every m no 3-cycle through m lies inside W(m) + {m}
//   Mut      balanced, and no 3-cycle on a triple of pairwise *mutual* vertices
//            (x,y mutual: each lies in the other's window)
// plus the histogram of the number of 3-cycles among balanced tournaments and its mean
// (a uniformly random tournament has mean C(N,3)/4).
// earl[v] = bitmask of the vertices that are earlier than v.
// usage: btenum N
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static int N;
static uint32_t Lm[16], Rm[16], Wm[16], earl[16];
static int lastv[16];
static unsigned long long cB, cT, cW, cLoc, cMut, hist[200];
static int mut[16][16];

static inline int pc(uint32_t x) { return __builtin_popcount(x); }

static void leaf(void) {
    cB++;
    int s = 0;
    for (int v = 0; v < N; v++) { int d = pc(earl[v]); s += d * (d - 1) / 2; }
    int c3 = N * (N - 1) * (N - 2) / 6 - s;
    hist[c3]++;
    if (c3 == 0) cT++;
    int okW = 1, okL = 1;
    for (int m = 0; m < N; m++) {
        uint32_t U = Wm[m] | (1u << m);
        int k = pc(U), t = 0;
        for (int v = 0; v < N; v++) if (U >> v & 1) { int d = pc(earl[v] & U); t += d * (d - 1) / 2; }
        if (t != k * (k - 1) * (k - 2) / 6) okW = 0;
        uint32_t in = earl[m] & Wm[m], out = Wm[m] & ~earl[m];
        for (int x = 0; x < N; x++) if (in >> x & 1) if (earl[x] & out) { okL = 0; break; }
    }
    cW += okW; cLoc += okL;
    int okM = 1;
    for (int x = 0; x < N && okM; x++) for (int y = x + 1; y < N && okM; y++) if (mut[x][y])
        for (int z = y + 1; z < N; z++) if (mut[x][z] && mut[y][z]) {
            int a = earl[y] >> x & 1, b = earl[z] >> y & 1, c = earl[x] >> z & 1;   // x<y, y<z, z<x
            if (a == b && b == c) { okM = 0; break; }
        }
    cMut += okM;
}

static void rec(int y) {
    if (y == N) { leaf(); return; }
    uint32_t save[16];
    for (int v = 0; v < N; v++) save[v] = earl[v];
    for (uint32_t E = 0; E < (1u << y); E++) {
        earl[y] = E;
        for (int x = 0; x < y; x++) earl[x] = (E >> x & 1) ? save[x] : (save[x] | (1u << y));
        int ok = 1;
        for (int v = 0; v <= y; v++)
            if (lastv[v] == y && pc(earl[v] & Lm[v]) != pc(earl[v] & Rm[v])) { ok = 0; break; }
        if (ok) rec(y + 1);
    }
    for (int v = 0; v < N; v++) earl[v] = save[v];
}

int main(int argc, char **argv) {
    N = atoi(argv[1]);
    for (int m = 1; m <= N; m++) {
        int r = (m - 1 < N - m) ? m - 1 : N - m;
        Lm[m - 1] = Rm[m - 1] = 0;
        for (int e = 1; e <= r; e++) { Lm[m - 1] |= 1u << (m - 1 - e); Rm[m - 1] |= 1u << (m - 1 + e); }
        Wm[m - 1] = Lm[m - 1] | Rm[m - 1];
        lastv[m - 1] = m - 1 + r;
    }
    for (int x = 0; x < N; x++) for (int y = 0; y < N; y++)
        mut[x][y] = (Wm[x] >> y & 1) && (Wm[y] >> x & 1);
    rec(0);
    double mean = 0;
    for (int c = 0; c < 200; c++) mean += (double)c * hist[c];
    mean /= cB;
    printf("N=%d B=%llu transitive=%llu window-transitive=%llu locally-transitive=%llu mutual-triangle-free=%llu mean3cyc=%.4f (random: %.4f)\n",
           N, cB, cT, cW, cLoc, cMut, mean, N * (N - 1) * (N - 2) / 24.0);
    printf("  3-cycle histogram:");
    for (int c = 0; c < 200; c++) if (hist[c]) printf(" %d:%llu", c, hist[c]);
    printf("\n");
    return 0;
}

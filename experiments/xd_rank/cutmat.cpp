// Connection ("cut") matrices of the semi-symmetric fold count.
//
// For a partition [N] = X u Y, M[sigma, tau] = number of interleavings (shuffles) of an
// ordering sigma of X and an ordering tau of Y that are valid N-sequences.
// a(N) = sum of all entries.  We enumerate the a(N) valid sequences once per cut and
// bucket them by (sigma, tau).  Reported for each cut:
//   nzr / nzc   nonzero rows / columns          (trivial bounds |X|!, |Y|!)
//   dr / dc     distinct nonzero rows / columns
//   rank        rank modulo p = 2^31 - 1 (a lower bound for the rank over Q; exact
//               whenever it equals min(dr, dc))
//   valid x valid: the same for the submatrix whose rows / columns are valid sequences
//               of the relabelled strips [|X|], [|Y|]
//
// usage: cutmat N kind [param ...] [dump FILE]
//   kind = parity | spatial j | res q r | ed d | mask HEX
//   "dump FILE": write the nonzero rows (ordering of X, then the row) to FILE
// build: g++ -O3 -march=native -o cutmat.bin cutmat.cpp
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <string>
#include <algorithm>
#include <unordered_map>
using namespace std;
typedef uint64_t u64; typedef uint32_t u32;

static int N; static u32 lm[32], rm_[32];
static u32 X;                       // bitmask of X (bit p = panel p+1)
static int kx, ky; static int posX[32], posY[32];
static u64 fact[21];
static vector<u32> Mat; static u64 nr, nc;      // dense, row-major, compact indices
static unordered_map<u64,int> rowId, colId;     // full rank -> compact index
static int pass; static u64 total;
static int seq[32];

static inline u64 lehmer(const int *a, int k) { // rank of the relative order
    u64 r = 0;
    for (int i = 0; i < k; i++) { int c = 0; for (int j = i + 1; j < k; j++) c += a[j] < a[i]; r += c * fact[k - 1 - i]; }
    return r;
}
static void unrank(u64 r, int k, int *a) {       // inverse of lehmer: values 0..k-1
    bool used[32] = {0};
    for (int i = 0; i < k; i++) { u64 c = r / fact[k - 1 - i]; r %= fact[k - 1 - i];
        int v = 0; for (;; v++) if (!used[v]) { if (c == 0) break; c--; }
        used[v] = 1; a[i] = v; }
}
static void leaf() {
    int a[32], b[32]; int i = 0, j = 0;
    for (int t = 0; t < N; t++) { int p = seq[t]; if (X >> p & 1) a[i++] = posX[p]; else b[j++] = posY[p]; }
    u64 ra = lehmer(a, kx), rb = lehmer(b, ky);
    if (pass == 0) { rowId.emplace(ra, 0); colId.emplace(rb, 0); total++; }
    else Mat[(u64)rowId[ra] * nc + colId[rb]]++;
}
static void rec(u32 s, int depth) {
    if (depth == N) { leaf(); return; }
    for (int p = 0; p < N; p++) if (!(s >> p & 1) && __builtin_popcount(s & lm[p]) == __builtin_popcount(s & rm_[p])) {
        seq[depth] = p; rec(s | 1u << p, depth + 1); }
}
// validity of a sequence (values 0..k-1) on the strip [k]
static bool validSeq(const int *a, int k) {
    u32 s = 0;
    for (int t = 0; t < k; t++) { int p = a[t]; int r = min(p, k - 1 - p); u32 l = 0, rr = 0;
        for (int d = 1; d <= r; d++) { l += s >> (p - d) & 1; rr += s >> (p + d) & 1; }
        if (l != rr) return false; s |= 1u << p; }
    return true;
}
static const u64 P = 2147483647ULL;
static u64 pw(u64 a, u64 e) { u64 r = 1; a %= P; while (e) { if (e & 1) r = r * a % P; a = a * a % P; e >>= 1; } return r; }
// rank mod P (destroys A)
static int rankModP(vector<vector<u32>> &A) {
    int n = A.size(); if (!n) return 0; int m = A[0].size(); int rk = 0;
    vector<char> usedRow(n, 0);
    for (int c = 0; c < m && rk < n; c++) {
        int piv = -1; for (int i = 0; i < n; i++) if (!usedRow[i] && A[i][c]) { piv = i; break; }
        if (piv < 0) continue;
        usedRow[piv] = 1; rk++;
        u64 inv = pw(A[piv][c], P - 2); u32 *pr = A[piv].data();
        for (int i = 0; i < n; i++) if (!usedRow[i] && A[i][c]) {
            u64 f = P - (u64)A[i][c] * inv % P; u32 *ri = A[i].data();
            for (int j = c; j < m; j++) ri[j] = (ri[j] + f * pr[j]) % P;
        }
    }
    return rk;
}
struct Stats { u64 nzr, nzc, dr, dc; int rank; };
static Stats analyse(const vector<int> &R, const vector<int> &C) {
    Stats st;
    vector<int> R2, C2; vector<char> cnz(C.size(), 0);
    for (int r : R) { bool nz = false; const u32 *row = &Mat[(u64)r * nc];
        for (size_t j = 0; j < C.size(); j++) if (row[C[j]]) { nz = true; cnz[j] = 1; }
        if (nz) R2.push_back(r); }
    for (size_t j = 0; j < C.size(); j++) if (cnz[j]) C2.push_back(C[j]);
    st.nzr = R2.size(); st.nzc = C2.size();
    vector<vector<u32>> rows; rows.reserve(R2.size());
    for (int r : R2) { vector<u32> v(C2.size()); const u32 *row = &Mat[(u64)r * nc];
        for (size_t j = 0; j < C2.size(); j++) v[j] = row[C2[j]]; rows.push_back(std::move(v)); }
    sort(rows.begin(), rows.end()); rows.erase(unique(rows.begin(), rows.end()), rows.end());
    st.dr = rows.size();
    size_t n = rows.size(), m = C2.size();
    vector<vector<u32>> cols(m, vector<u32>(n));
    for (size_t i = 0; i < n; i++) for (size_t j = 0; j < m; j++) cols[j][i] = rows[i][j];
    rows.clear(); rows.shrink_to_fit();
    sort(cols.begin(), cols.end()); cols.erase(unique(cols.begin(), cols.end()), cols.end());
    st.dc = cols.size();
    st.rank = rankModP(cols);
    return st;
}
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: cutmat N kind [params] [dump FILE]\n"); return 1; }
    N = atoi(argv[1]); string kind = argv[2]; string label = kind; const char *dump = 0;
    X = 0; int ai = 3;
    if (kind == "parity") { for (int p = 0; p < N; p += 2) X |= 1u << p; }
    else if (kind == "spatial") { int j = atoi(argv[ai++]); X = (1u << j) - 1; label += "_" + to_string(j); }
    else if (kind == "res") { int q = atoi(argv[ai++]), r = atoi(argv[ai++]); for (int p = 0; p < N; p++) if ((p + 1) % q == r) X |= 1u << p; label += "_" + to_string(q) + "_" + to_string(r); }
    else if (kind == "ed") { int d = atoi(argv[ai++]); for (int p = 0; p < N; p++) { int x = (p + 1) % d; if (x && x % 2 == 0) X |= 1u << p; } label += "_" + to_string(d); }
    else if (kind == "mask") { X = strtoul(argv[ai++], 0, 16); label += string("_") + argv[ai - 1]; }
    else { fprintf(stderr, "unknown kind\n"); return 1; }
    if (ai + 1 < argc && string(argv[ai]) == "dump") dump = argv[ai + 1];
    fact[0] = 1; for (int i = 1; i <= 20; i++) fact[i] = fact[i - 1] * i;
    for (int p = 0; p < N; p++) { int r = min(p, N - 1 - p); lm[p] = rm_[p] = 0; for (int d = 1; d <= r; d++) { lm[p] |= 1u << (p - d); rm_[p] |= 1u << (p + d); } }
    kx = ky = 0; for (int p = 0; p < N; p++) if (X >> p & 1) posX[p] = kx++; else posY[p] = ky++;
        pass = 0; total = 0; rec(0, 0);
    nr = nc = 0; { vector<u64> ks; for (auto &v : rowId) ks.push_back(v.first); sort(ks.begin(), ks.end()); for (u64 k : ks) rowId[k] = nr++;
      ks.clear(); for (auto &v : colId) ks.push_back(v.first); sort(ks.begin(), ks.end()); for (u64 k : ks) colId[k] = nc++; }
    Mat.assign(nr * nc, 0); pass = 1; rec(0, 0);
    vector<int> R(nr), C(nc); for (u64 i = 0; i < nr; i++) R[i] = i; for (u64 j = 0; j < nc; j++) C[j] = j;
    Stats s = analyse(R, C);
    vector<int> RV, CV; int a[32]; u64 vx = 0, vy = 0;
    for (auto &kv : rowId) { unrank(kv.first, kx, a); if (validSeq(a, kx)) { vx++; RV.push_back(kv.second); } }
    for (auto &kv : colId) { unrank(kv.first, ky, a); if (validSeq(a, ky)) { vy++; CV.push_back(kv.second); } }
    sort(RV.begin(), RV.end()); sort(CV.begin(), CV.end());
    Stats v = analyse(RV, CV);
    u64 sumV = 0; for (int r : RV) for (int c : CV) sumV += Mat[(u64)r * nc + c];
    printf("N=%d cut=%s |X|=%d |Y|=%d a=%llu | all: nzr=%llu nzc=%llu dr=%llu dc=%llu rank=%d (|X|!=%llu |Y|!=%llu) | "
           "valid x valid: vr=%llu vc=%llu nzr=%llu nzc=%llu dr=%llu dc=%llu rank=%d sum=%llu\n",
           N, label.c_str(), kx, ky, (unsigned long long)total,
           (unsigned long long)s.nzr, (unsigned long long)s.nzc, (unsigned long long)s.dr, (unsigned long long)s.dc, s.rank,
           (unsigned long long)fact[kx], (unsigned long long)fact[ky],
           (unsigned long long)vx, (unsigned long long)vy, (unsigned long long)v.nzr, (unsigned long long)v.nzc,
           (unsigned long long)v.dr, (unsigned long long)v.dc, v.rank, (unsigned long long)sumV);
    fflush(stdout);
    if (dump) {
        FILE *f = fopen(dump, "w");
        int xs[32], ys[32], kk = 0; for (int p = 0; p < N; p++) if (X >> p & 1) xs[kk++] = p + 1;
        kk = 0; for (int p = 0; p < N; p++) if (!(X >> p & 1)) ys[kk++] = p + 1;
        fprintf(f, "# cols:"); { vector<u64> ks; for (auto &v : colId) ks.push_back(v.first); sort(ks.begin(), ks.end()); for (u64 r : ks) { unrank(r, ky, a); fprintf(f, " "); for (int i = 0; i < ky; i++) fprintf(f, "%s%d", i ? "," : "", ys[a[i]]); } } fprintf(f, "\n");
        vector<u64> ks; for (auto &v : rowId) ks.push_back(v.first); sort(ks.begin(), ks.end());
        for (u64 r : ks) { unrank(r, kx, a);
            for (int i = 0; i < kx; i++) fprintf(f, "%s%d", i ? "," : "", xs[a[i]]);
            fprintf(f, " :"); const u32 *row = &Mat[(u64)rowId[r] * nc]; for (u64 j = 0; j < nc; j++) fprintf(f, " %u", row[j]); fprintf(f, "\n"); }
        fclose(f);
    }
    return 0;
}

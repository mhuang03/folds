// nf.cpp -- trace normal forms: a(N) from g stored only on NORMAL-FORM sets.
//
// tau(T) = for each element t of T, (#T in the left arm of t, #T in the right arm of t).
// g(T) depends only on tau(T) (which orderings of T are valid is decided by tau alone).
// A LEFT SHIFT moves one element p of T to p-1 (p-1 not in T); it is ADMISSIBLE when it
// does not change tau.  NF(T) = result of applying the leftmost admissible shift until
// none applies.  Then g(T) = g(NF(T)), and the pull DP closes on normal-form sets:
//      g(T) = sum_{p in T, (T-p, p) valid} g(NF(T - p))      for T in normal form.
// Modes:
//   nf.bin count N [threads]   number of normal-form sets in every layer j <= ceil(N/2)
//                              (no DP, any N <= 40 in principle; cost ~ 2^N * N^2)
//   nf.bin count2 N j [threads] the same for the single layer j
//   nf.bin dp N                a(N) by the MITM pairing with g stored on NF sets only
//                              (hash tables; N <= ~27); prints table sizes vs C(N,j)
// Environment NF_SUB=T restricts the shifts so that NF keeps the sub-block of
// rust/src/sub.rs with T high panels per side (T = 0: keeps the (|L|,|R|,c) block):
// no shift may move an element into, out of or inside the high parts or the middle panel.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <vector>
#include <unordered_map>
#include <thread>
#include <atomic>
#include <ctime>
using namespace std;
typedef unsigned long long u64;
typedef unsigned __int128 u128;
static int N;
static u64 lm[64], rm_[64];
static u64 forbid = 0;   // bit p set: the shift p -> p-1 is not allowed (restricted NF)
static inline bool valid(u64 s, int p) {
    return __builtin_popcountll(s & lm[p]) == __builtin_popcountll(s & rm_[p]);
}
// is the shift p -> p-1 (p in t, p-1 not in t) trace-preserving?
static inline bool shift_ok(u64 t, int p) {
    u64 t2 = t ^ (1ULL << p) ^ (1ULL << (p - 1));
    // the moved element itself
    if (__builtin_popcountll(t & lm[p]) != __builtin_popcountll(t2 & lm[p - 1])) return false;
    if (__builtin_popcountll(t & rm_[p]) != __builtin_popcountll(t2 & rm_[p - 1])) return false;
    // every other element e keeps its position, and an arm A of e changes its count by
    // [p in A] - [p-1 in A]: the trace is kept iff no arm holds exactly one of p-1, p
    u64 rest = t & ~(1ULL << p);
    u64 two = (1ULL << p) | (1ULL << (p - 1));
    for (u64 x = rest; x; x &= x - 1) {
        int e = __builtin_ctzll(x);
        u64 a = lm[e] & two, b = rm_[e] & two;
        if ((a != 0 && a != two) || (b != 0 && b != two)) return false;
    }
    return true;
}
static inline bool is_nf(u64 t) {
    // candidates: p in t, p-1 not in t, p >= 1
    u64 c = t & ~(t << 1) & ~1ULL & ~forbid;
    for (; c; c &= c - 1)
        if (shift_ok(t, __builtin_ctzll(c))) return false;
    return true;
}
static inline u64 nf(u64 t) {
    for (;;) {
        u64 c = t & ~(t << 1) & ~1ULL & ~forbid;
        bool moved = false;
        for (; c; c &= c - 1) {
            int p = __builtin_ctzll(c);
            if (shift_ok(t, p)) { t ^= (1ULL << p) ^ (1ULL << (p - 1)); moved = true; break; }
        }
        if (!moved) return t;
    }
}
static u64 binom(int n, int k) {
    if (k < 0 || k > n) return 0;
    u128 c = 1;
    for (int i = 0; i < k; i++) c = c * (n - i) / (i + 1);
    return (u64)c;
}
// enumerate all j-subsets of [0,N) split into chunks by the top bits (for threads)
static u64 next_comb(u64 x) { u64 c = x & -x, r = x + c; return (((r ^ x) >> 2) / c) | r; }

// NF_HALF=1: count only sets in stored mirror blocks, |L| <= |R| (the denominator is
// then the number of such sets, about C(N,j)/2: the ratio is relative to stored words)
static bool half_mode = false;
static u64 g_den = 0;
static inline bool keep(u64 t) {
    if (!half_mode) return true;
    int h = N / 2;
    u64 low = (1ULL << h) - 1, high = ((1ULL << N) - 1) ^ ((1ULL << (N - h)) - 1);
    return __builtin_popcountll(t & low) <= __builtin_popcountll(t & high);
}
static void count_layer(int j, int T, u64* out_nf) {
    // split by the highest element h of the set: subsets with max element h
    atomic<int> nexth(j - 1);
    vector<u64> part(T, 0), dens(T, 0);
    auto work = [&](int id) {
        for (;;) {
            int h = nexth++;
            if (h >= N) break;
            if (j == 0) break;
            u64 cnt = 0;
            int k = j - 1;
            u64 den = 0;
            if (k == 0) { u64 t = 1ULL << h; if (keep(t)) { den++; cnt += is_nf(t); } }
            else {
                u64 x = (1ULL << k) - 1, lim = 1ULL << h;
                for (; x < lim; x = next_comb(x)) {
                    u64 t = x | (1ULL << h);
                    if (!keep(t)) continue;
                    den++;
                    cnt += is_nf(t);
                }
            }
            part[id] += cnt;
            dens[id] += den;
        }
    };
    vector<thread> th;
    for (int i = 0; i < T; i++) th.emplace_back(work, i);
    for (auto& t : th) t.join();
    u64 s = 0, d = 0;
    for (auto v : part) s += v;
    for (auto v : dens) d += v;
    if (j == 0) s = d = 1;
    *out_nf = s;
    g_den = d;
}

int main(int argc, char** argv) {
    if (argc < 3) { fprintf(stderr, "usage: nf.bin count N [threads] | count2 N j [threads] | dp N\n"); return 1; }
    const char* mode = argv[1];
    N = atoi(argv[2]);
    for (int p = 0; p < N; p++) {
        int r = p < N - 1 - p ? p : N - 1 - p;
        lm[p] = rm_[p] = 0;
        for (int d = 1; d <= r; d++) { lm[p] |= 1ULL << (p - d); rm_[p] |= 1ULL << (p + d); }
    }
    if (getenv("NF_SUB")) {
        int T = atoi(getenv("NF_SUB")), h = N / 2, a = h - T;
        // protected panels: high left [a, h), middle (odd N), high right [N-h, N-a)
        u64 prot = 0;
        for (int p = a; p < N - a; p++) prot |= 1ULL << p;
        if (T == 0) { prot = 0; for (int p = h; p < N - h; p++) prot |= 1ULL << p; }
        // shift p -> p-1 forbidden if p or p-1 is protected, or it crosses the middle
        for (int p = 1; p < N; p++) {
            bool bad = (prot >> p & 1) || (prot >> (p - 1) & 1) || (p == h && N % 2 == 0) || (p == N - a && T == 0);
            if (T == 0 && N % 2 == 0 && p == h) bad = true;
            if (bad) forbid |= 1ULL << p;
        }
    }
    if (!strcmp(mode, "bench")) {
        // cost of NF(T - p) for random j-sets T and all p: the lookup cost of an NF-DP
        int j = atoi(argv[3]);
        u64 seed = 88172645463325252ULL, sink = 0, calls = 0, moved = 0;
        auto rnd = [&]() { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; return seed; };
        struct timespec t0, t1;
        clock_gettime(CLOCK_MONOTONIC, &t0);
        for (int it = 0; it < 200000; it++) {
            u64 t = 0;
            while (__builtin_popcountll(t) < j) t |= 1ULL << (rnd() % N);
            for (u64 y = t; y; y &= y - 1) {
                u64 pre = t & ~(y & -y);
                u64 q = nf(pre);
                moved += q != pre;
                sink ^= q;
                calls++;
            }
        }
        clock_gettime(CLOCK_MONOTONIC, &t1);
        double ns = ((t1.tv_sec - t0.tv_sec) * 1e9 + (t1.tv_nsec - t0.tv_nsec)) / calls;
        printf("N=%d j=%d: %.1f ns per NF call, %.3f of the calls move (sink %llx)\n", N, j, ns, (double)moved / calls, sink & 1);
        return 0;
    }
    if (!strcmp(mode, "count") || !strcmp(mode, "count2")) {
        half_mode = getenv("NF_HALF") && atoi(getenv("NF_HALF"));
        int T = 3, jlo = 0, jhi = (N + 1) / 2;
        if (!strcmp(mode, "count2")) { jlo = jhi = atoi(argv[3]); if (argc > 4) T = atoi(argv[4]); }
        else if (argc > 3) T = atoi(argv[3]);
        for (int j = jlo; j <= jhi; j++) {
            u64 c;
            count_layer(j, T, &c);
            u64 b = g_den;
            printf("N=%d j=%2d sub=%s half=%d sets=%llu nf=%llu ratio=%.4f\n", N, j, getenv("NF_SUB") ? getenv("NF_SUB") : "none", (int)half_mode, b, c, (double)c / b);
            fflush(stdout);
        }
        return 0;
    }
    // dp mode
    int h = N / 2;
    int top = (N % 2 == 0) ? h : h;   // stored layers 0..top
    vector<unordered_map<u64, u64>> G(top + 1);
    G[0][0] = 1;
    for (int j = 1; j <= top; j++) {
        u64 x = (1ULL << j) - 1, lim = 1ULL << N;
        for (; x < lim; x = next_comb(x)) {
            if (!is_nf(x)) continue;
            u64 acc = 0;
            for (u64 y = x; y; y &= y - 1) {
                int p = __builtin_ctzll(y);
                u64 pre = x & ~(1ULL << p);
                if (!valid(pre, p)) continue;
                auto it = G[j - 1].find(nf(pre));
                if (it == G[j - 1].end()) { fprintf(stderr, "missing NF!\n"); return 2; }
                acc += it->second;
            }
            G[j][x] = acc;
        }
        printf("layer %2d: C(N,j)=%llu stored(NF)=%zu ratio=%.4f\n", j, binom(N, j), G[j].size(), (double)G[j].size() / binom(N, j));
    }
    u128 a = 0;
    u64 full = (1ULL << N) - 1;
    if (N % 2 == 0) {
        u64 x = (1ULL << h) - 1, lim = 1ULL << N;
        for (; x < lim; x = next_comb(x)) a += (u128)G[h][nf(x)] * G[h][nf(full & ~x)];
    } else {
        // fused: sum_{|U|=h+1} g(U) g(U^c), g(U) on the fly from layer h
        u64 x = (1ULL << (h + 1)) - 1, lim = 1ULL << N;
        for (; x < lim; x = next_comb(x)) {
            u64 gu = 0;
            for (u64 y = x; y; y &= y - 1) {
                int p = __builtin_ctzll(y);
                u64 pre = x & ~(1ULL << p);
                if (valid(pre, p)) gu += G[h][nf(pre)];
            }
            if (gu) a += (u128)gu * G[h][nf(full & ~x)];
        }
    }
    char buf[64]; int n = 0; u128 v = a;
    if (!v) buf[n++] = '0';
    while (v) { buf[n++] = '0' + (int)(v % 10); v /= 10; }
    printf("a(%d) = ", N);
    while (n) putchar(buf[--n]);
    printf("\n");
}

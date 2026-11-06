// trace.cpp -- the TRACE of a set T on the windows, and how much it compresses.
//
// For T = {t_1 < ... < t_j} and each element t_l, let a_l <= l <= b_l be the index range
// of the elements of T inside the window of t_l: left arm = t_{a_l..l-1}, right arm =
// t_{l+1..b_l}.  The trace is tau(T) = ((a_l, b_l))_l.  The whole PAST of T (which
// orderings of T are valid) depends only on tau(T), and tau(T \ t_i) is a function of
// tau(T) and i, so g(T) = G(tau(T)) and G satisfies the trace recursion
//      G(tau) = sum_{i : i - a_i = b_i - i} G(tau - i).
// This program counts, per layer j, the distinct traces (mirror-identified) among sets
// with g > 0, checks that g is constant on every trace fibre, and compares with the
// number of mirror orbits.
// usage: trace.bin N [first layer]
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <unordered_map>
#include <string>
#include <algorithm>
using namespace std;
typedef unsigned long long u64;
static int N;
static u64 lm[64], rm_[64];
static inline bool valid(u64 s, int p) {
    return __builtin_popcountll(s & lm[p]) == __builtin_popcountll(s & rm_[p]);
}
// trace as a byte string: for each element, (#elements of T in left arm, #in right arm)
// (equivalent to (a_l, b_l) given l).
static string trace_of(u64 t) {
    string s;
    for (u64 x = t; x; x &= x - 1) {
        int p = __builtin_ctzll(x);
        s.push_back((char)__builtin_popcountll(t & lm[p]));
        s.push_back((char)__builtin_popcountll(t & rm_[p]));
    }
    return s;
}
static string mirror_trace(const string& s) {
    string r;
    for (int i = (int)s.size() - 2; i >= 0; i -= 2) { r.push_back(s[i + 1]); r.push_back(s[i]); }
    return r;
}
int main(int argc, char** argv) {
    N = atoi(argv[1]);
    for (int p = 0; p < N; p++) {
        int r = min(p, N - 1 - p);
        lm[p] = rm_[p] = 0;
        for (int d = 1; d <= r; d++) { lm[p] |= 1ULL << (p - d); rm_[p] |= 1ULL << (p + d); }
    }
    u64 M = 1ULL << N;
    vector<u64> g(M, 0);
    g[0] = 1;
    for (u64 s = 1; s < M; s++) {
        u64 acc = 0;
        for (u64 t = s; t; t &= t - 1) {
            int p = __builtin_ctzll(t);
            u64 pre = s & ~(1ULL << p);
            if (g[pre] && valid(pre, p)) acc += g[pre];
        }
        g[s] = acc;
    }
    int H = N / 2;
    printf("# N=%d  j  C(N,j)  g>0  orbits(g>0)  traces(g>0, mirror-identified)  ratio  gfibre_ok\n", N);
    u64 totT = 0, totO = 0;
    int j0 = argc > 2 ? atoi(argv[2]) : 0;
    for (int j = j0; j <= H; j++) {
        unordered_map<string, u64> T;
        u64 cnt = 0, orb = 0, bad = 0, c = 0;
        for (u64 s = 0; s < M; s++) {
            if (__builtin_popcountll(s) != j) continue;
            c++;
            if (!g[s]) continue;
            cnt++;
            u64 m = 0;
            for (int i = 0; i < N; i++) if (s >> i & 1) m |= 1ULL << (N - 1 - i);
            if (s <= m) orb++;
            string a = trace_of(s), b = mirror_trace(a);
            string key = min(a, b);
            auto it = T.find(key);
            if (it == T.end()) T.emplace(key, g[s]);
            else if (it->second != g[s]) bad++;
        }
        printf("%2d %10llu %10llu %10llu %10zu %.4f %s\n", j, c, cnt, orb, T.size(), (double)T.size() / orb, bad ? "BAD" : "ok");
        totT += T.size();
        totO += orb;
    }
    printf("TOTAL N=%d layers<=%d orbits=%llu traces=%llu ratio=%.4f\n", N, H, totO, totT, (double)totT / totO);
}

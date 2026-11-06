// bisim.cpp -- how much can the subset DP state S be compressed, exactly?
//
// For each layer k = |S| it prints, over the LIVE sets (g(S) > 0 and f(S) > 0):
//   live      number of live k-sets (this is also the exact minimal number of states at
//             time k of ANY automaton that reads the sequence in time order and accepts
//             exactly the valid sequences: Hankel/Myhill-Nerode argument, see NOTES.txt)
//   orbits    live mirror orbits
//   fvals     distinct values of f(S)            (lower bound for any exact "predictor")
//   gfvals    distinct pairs (g(S), f(S))        (what a MITM layer has to deliver)
//   bisimF    classes of the coarsest COUNTING BISIMULATION for the backward DP
//             f(S) = sum_{valid p} f(S+p): S ~ S' iff the multisets of classes of their
//             live successors agree.  This is the smallest state space of any DP whose
//             state is a function of S and which is consistent with the transitions.
//   bisimG    the same for the forward DP g (predecessor multisets), from the bottom.
//   defF      number of fibres of the imbalance vector J_S(m) over ALL panels m
//             (the "window imbalance" key; it does not mark which panels are placed) and how many of them have non-constant f.
// usage: bisim.bin N
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <vector>
#include <unordered_map>
#include <map>
#include <algorithm>
#include <string>
using namespace std;
typedef unsigned long long u64;
typedef unsigned __int128 u128;

static int N;
static u64 lm[64], rm_[64];
static inline bool valid(u64 s, int p) {
    return __builtin_popcountll(s & lm[p]) == __builtin_popcountll(s & rm_[p]);
}
static u64 mirror(u64 s) {
    u64 t = 0;
    for (int i = 0; i < N; i++) if (s >> i & 1) t |= 1ULL << (N - 1 - i);
    return t;
}
struct VH {
    size_t operator()(const vector<uint32_t>& v) const {
        u64 h = 1469598103934665603ULL;
        for (auto x : v) { h ^= x; h *= 1099511628211ULL; h ^= h >> 29; }
        return h;
    }
};
struct PH {
    size_t operator()(const pair<u64, u64>& p) const { return p.first * 0x9E3779B97F4A7C15ULL ^ (p.second + (p.first >> 17)); }
};

int main(int argc, char** argv) {
    N = atoi(argv[1]);
    for (int p = 0; p < N; p++) {
        int r = min(p, N - 1 - p);
        lm[p] = rm_[p] = 0;
        for (int d = 1; d <= r; d++) { lm[p] |= 1ULL << (p - d); rm_[p] |= 1ULL << (p + d); }
    }
    u64 M = 1ULL << N, full = M - 1;
    vector<u64> g(M, 0), f(M, 0);
    // forward g in order of increasing integer value (subsets come before supersets)
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
    f[full] = 1;
    for (u64 s = full; s-- > 0;) {
        u64 acc = 0;
        for (u64 t = full & ~s; t; t &= t - 1) {
            int p = __builtin_ctzll(t);
            if (valid(s, p)) acc += f[s | (1ULL << p)];
        }
        f[s] = acc;
    }
    printf("# N=%d a(N)=%llu (check f(0)=g(full): %s)\n", N, (unsigned long long)f[0], f[0] == g[full] ? "ok" : "MISMATCH");
    // layer lists
    vector<vector<u64>> layer(N + 1);
    for (u64 s = 0; s < M; s++) if (g[s] && f[s]) layer[__builtin_popcountll(s)].push_back(s);
    // backward bisimulation classes (0 = not live)
    vector<uint32_t> cf(M, 0), cg(M, 0);
    vector<size_t> nbF(N + 1), nbG(N + 1);
    for (int k = N; k >= 0; k--) {
        unordered_map<vector<uint32_t>, uint32_t, VH> H;
        for (u64 s : layer[k]) {
            vector<uint32_t> v;
            for (u64 t = full & ~s; t; t &= t - 1) {
                int p = __builtin_ctzll(t);
                u64 nx = s | (1ULL << p);
                if (valid(s, p) && cf[nx]) v.push_back(cf[nx]);
            }
            sort(v.begin(), v.end());
            auto it = H.find(v);
            if (it == H.end()) { uint32_t id = H.size() + 1; H.emplace(v, id); cf[s] = id; }
            else cf[s] = it->second;
        }
        nbF[k] = H.size();
    }
    for (int k = 0; k <= N; k++) {
        unordered_map<vector<uint32_t>, uint32_t, VH> H;
        for (u64 s : layer[k]) {
            vector<uint32_t> v;
            for (u64 t = s; t; t &= t - 1) {
                int p = __builtin_ctzll(t);
                u64 pr = s & ~(1ULL << p);
                if (valid(pr, p) && cg[pr]) v.push_back(cg[pr]);
            }
            sort(v.begin(), v.end());
            auto it = H.find(v);
            if (it == H.end()) { uint32_t id = H.size() + 1; H.emplace(v, id); cg[s] = id; }
            else cg[s] = it->second;
        }
        nbG[k] = H.size();
    }
    printf("# k C(N,k) live orbits fvals gfvals bisimF bisimG defFibres defBad\n");
    u64 tot[9] = {0};
    for (int k = 0; k <= N; k++) {
        size_t orbits = 0;
        unordered_map<u64, int> fv;
        unordered_map<pair<u64, u64>, int, PH> gfv;
        map<vector<int>, pair<u64, int>> def;  // key -> (f value, consistent?)
        size_t bad = 0;
        for (u64 s : layer[k]) {
            u64 m = mirror(s);
            if (s <= m) orbits++;
            fv[f[s]] = 1;
            gfv[{g[s], f[s]}] = 1;
            // cyclic defect at free panels: I(m) = Ptilde(2m-1) - 2P(m-1), m = p+1
            vector<int> key;
            for (int p = 0; p < N; p++) {
                int lc = __builtin_popcountll(s & lm[p]), rc = __builtin_popcountll(s & rm_[p]);
                key.push_back(rc - lc);
            }
            auto it = def.find(key);
            if (it == def.end()) def[key] = {f[s], 1};
            else if (it->second.first != f[s] && it->second.second) { it->second.second = 0; bad++; }
        }
        // binomial
        u64 c = 1;
        for (int i = 0; i < k; i++) c = c * (N - i) / (i + 1);
        printf("%2d %10llu %10zu %10zu %10zu %10zu %10zu %10zu %10zu %6zu\n", k, c, layer[k].size(), orbits, fv.size(), gfv.size(), nbF[k], nbG[k], def.size(), bad);
        u64 row[9] = {c, layer[k].size(), orbits, fv.size(), gfv.size(), nbF[k], nbG[k], def.size(), bad};
        for (int i = 0; i < 9; i++) tot[i] += row[i];
    }
    printf("TOTAL N=%d sets=%llu live=%llu orbits=%llu fvals=%llu gfvals=%llu bisimF=%llu bisimG=%llu defFibres=%llu defBad=%llu\n", N,
           tot[0], tot[1], tot[2], tot[3], tot[4], tot[5], tot[6], tot[7], tot[8]);
    return 0;
}

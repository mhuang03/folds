// rec.cpp : iterate Theorem R (odd q, even nu), block composition (even q) and the mirror,
// carrying precedence constraints P ("a before b" on the order pi itself).
//   C(n, nu, P) = { pi in GoodL(n, nu) : pi satisfies P }.
// Moves at a node (all exact equivalences of GoodL): reverse, sig o pi, mirror (odd n, odd nu).
// Decompositions:
//   n = 2m+1, nu = 2w, w < m :  pi = oddE(alpha) ++ rev(evE(beta))     (goodL_oddR)
//        alpha in C(m+1, w, P_odd + sig(NotAgree psiW)),  beta in C(m, w, rev(P_even) + sig(NotAgree chiW))
//        cross pairs must be (odd before even).
//   n = 2m, nu = 2c+e : pi = block(b1) ++ block(b2), {b1,b2} = {1,2}  (good_comp, j = 2)
//        odd block (b=1) in C(m, e ? (c+1)%m : c, P_odd), even block in C(m, c, P_even).
// Base: n <= BASE (or odd n with nu in {1, n-1}, n <= BASE2) exhaustive DFS.
// Every success is re-verified directly against GoodL + P.
// usage: rec qlo qhi K [BASE] [BASE2] [verbose]  -- all q in [qlo,qhi], 1 <= rho, K*rho < q
#include <bits/stdc++.h>
using namespace std;
typedef vector<pair<int,int>> PS;
static int BASE = 12, BASE2 = 24, VERB = 0, PALIN = 1, MIRALL = 1;
static int md(int x, int n) { return ((x - 1) % n + n) % n + 1; }
static int sg(int n, int nu, int t) { return ((nu - t) % n + n) % n + 1; }
static int reach(int N, int m) { return min(m - 1, N - m); }
static bool agree(int Q, int k, int fi, int fj, int i, int j) {
  bool l1 = (fi - reach(Q, fi) <= fj && fj < fi), r1 = (i - reach(k, i) <= j && j < i);
  bool l2 = (fi < fj && fj <= fi + reach(Q, fi)), r2 = (i < j && j <= i + reach(k, i));
  return l1 == r1 && l2 == r2;
}
static int psiW(int w, int y) { return y <= w ? 2 * y : 2 * y - 1; }
static int chiW(int w, int z) { return z <= w ? 2 * z - 1 : 2 * z; }
// strip validity + sig validity + precedences
static bool checkGood(int n, int nu, const vector<int>& p, const PS& P) {
  if ((int)p.size() != n) return false;
  vector<int> pos(n + 1, -1);
  for (int k = 0; k < n; k++) { if (p[k] < 1 || p[k] > n || pos[p[k]] >= 0) return false; pos[p[k]] = k; }
  for (auto& e : P) if (pos[e.first] > pos[e.second]) return false;
  for (int pass = 0; pass < 2; pass++) {
    vector<char> S(n + 2, 0);
    for (int k = 0; k < n; k++) {
      int t = pass ? sg(n, nu, p[k]) : p[k];
      int r = reach(n, t), a = 0, b = 0;
      for (int j = 1; j <= r; j++) { a += S[t - j]; b += S[t + j]; }
      if (a != b) return false;
      S[t] = 1;
    }
  }
  return true;
}
// ---------- exhaustive base solver ----------
static int bn, bnu; static uint64_t Lm[70], Rm[70], need[70]; static int bsg[70], ba[70];
static unordered_set<uint64_t> failed; static long nodes, budget = 20000000;
static inline bool val(uint64_t S, int t) { return __builtin_popcountll(S & Lm[t]) == __builtin_popcountll(S & Rm[t]); }
static bool dfs(int k, uint64_t S, uint64_t T) {
  if (k == bn) return true;
  if (failed.count(S)) return false;
  if (++nodes > budget) return false;
  for (int t = 1; t <= bn; t++) {
    if (S >> t & 1) continue;
    if ((need[t] & S) != need[t]) continue;
    int u = bsg[t];
    if (val(S, t) && val(T, u)) { ba[k] = t; if (dfs(k + 1, S | 1ULL << t, T | 1ULL << u)) return true; }
  }
  failed.insert(S); return false;
}
static long nbudget = 0;
static bool baseSolve(int n, int nu, const PS& P, vector<int>& out) {
  bn = n; bnu = nu;
  for (int t = 1; t <= n; t++) {
    int r = reach(n, t); Lm[t] = Rm[t] = 0;
    for (int j = 1; j <= r; j++) { Lm[t] |= 1ULL << (t - j); Rm[t] |= 1ULL << (t + j); }
    bsg[t] = sg(n, nu, t); need[t] = 0;
  }
  for (auto& e : P) need[e.second] |= 1ULL << e.first;
  failed.clear(); nodes = 0;
  bool ok = dfs(0, 0, 0);
  if (nodes > budget) nbudget++;
  if (ok) out.assign(ba, ba + n);
  return ok;
}
// ---------- recursion ----------
struct Res { bool ok; vector<int> ord; };
static map<string, Res> memo;
static map<string, int> stats;
static long nfail = 0;
static string key(int n, int nu, PS P) {
  string s = to_string(n) + "," + to_string(nu) + ":";
  for (auto& e : P) s += to_string(e.first) + ">" + to_string(e.second) + " ";
  return s;
}
static void canon(PS& P) { sort(P.begin(), P.end()); P.erase(unique(P.begin(), P.end()), P.end()); }
static bool solve(int n, int nu, PS P, vector<int>& out, int depth);
// decompositions without the symmetry moves
static bool decompose(int n, int nu, const PS& P, vector<int>& out, int depth) {
  if (n % 2 == 0) {
    int m = n / 2, c = nu / 2, e = nu % 2;
    int nuo = e ? (c + 1) % m : c, nue = c;
    PS Po, Pe; int cross = 0; // cross: bit1 = needs odd first, bit2 = needs even first
    for (auto& x : P) {
      int a = x.first, b = x.second;
      if (a % 2 == 1 && b % 2 == 1) Po.push_back({(a + 1) / 2, (b + 1) / 2});
      else if (a % 2 == 0 && b % 2 == 0) Pe.push_back({a / 2, b / 2});
      else if (a % 2 == 1) cross |= 1; else cross |= 2;
    }
    if (cross == 3) return false;
    canon(Po); canon(Pe);
    vector<int> A, B;
    if (!solve(m, nuo, Po, A, depth + 1)) return false;
    if (!solve(m, nue, Pe, B, depth + 1)) return false;
    out.clear();
    if (cross == 2) { for (int y : B) out.push_back(2 * y); for (int y : A) out.push_back(2 * y - 1); }
    else { for (int y : A) out.push_back(2 * y - 1); for (int y : B) out.push_back(2 * y); }
    return true;
  }
  if (nu % 2 == 1) {
    // palindromic chain (good_palin), nu = 4r+1
    if (nu % 4 != 1 || !PALIN) return false;
    int k = n / 2, r = (nu - 1) / 4;
    if (2 * r >= k) return false;
    auto phi = [&](int i) { return i <= r ? 2 * i : 2 * i + 1; };
    auto psi = [&](int i) { return i <= r ? 2 * i - 1 : 2 * i; };
    vector<int> typ(n + 1, -1), idx(n + 1, 0);
    for (int i = 1; i <= k; i++) { typ[phi(i)] = 0; idx[phi(i)] = i; }
    int t0 = 2 * r + 1; typ[t0] = 1;
    for (int t = 1; t <= n; t++) if (typ[t] < 0) { int u = sg(n, nu, t); if (typ[u] != 0) { fprintf(stderr, "palin map\n"); exit(1); } typ[t] = 2; idx[t] = idx[u]; }
    PS Pb;
    for (auto& x : P) {
      int a = x.first, b = x.second;
      if (typ[a] == 0 && typ[b] == 0) Pb.push_back({idx[a], idx[b]});
      else if (typ[a] == 2 && typ[b] == 2) Pb.push_back({idx[b], idx[a]});
      else if (typ[a] < typ[b]) {} else return false;
    }
    for (int i = 1; i <= k; i++) for (int j = 1; j <= k; j++) if (i != j) {
      if (!agree(n, k, phi(i), phi(j), i, j)) Pb.push_back({i, j});
      if (!agree(n, k, psi(i), psi(j), i, j)) Pb.push_back({sg(k, 2 * r, i), sg(k, 2 * r, j)});
    }
    canon(Pb);
    vector<int> B;
    if (!solve(k, 2 * r, Pb, B, depth + 1)) return false;
    out.clear();
    for (int y : B) out.push_back(phi(y));
    out.push_back(t0);
    for (int i = (int)B.size() - 1; i >= 0; i--) out.push_back(sg(n, nu, phi(B[i])));
    return true;
  }
  int m = n / 2, w = nu / 2;
  if (w >= m) return false;
  PS Pa, Pb;
  for (auto& x : P) {
    int a = x.first, b = x.second;
    if (a % 2 == 1 && b % 2 == 1) Pa.push_back({(a + 1) / 2, (b + 1) / 2});
    else if (a % 2 == 0 && b % 2 == 0) Pb.push_back({b / 2, a / 2});
    else if (a % 2 == 0) return false;
  }
  int k = m + 1;
  for (int i = 1; i <= k; i++) for (int j = 1; j <= k; j++) if (i != j)
    if (!agree(n, k, psiW(w, i), psiW(w, j), i, j)) Pa.push_back({sg(k, w, i), sg(k, w, j)});
  for (int i = 1; i <= m; i++) for (int j = 1; j <= m; j++) if (i != j)
    if (!agree(n, m, chiW(w, i), chiW(w, j), i, j)) Pb.push_back({sg(m, w, i), sg(m, w, j)});
  canon(Pa); canon(Pb);
  vector<int> A, B;
  if (!solve(k, w, Pa, A, depth + 1)) return false;
  if (!solve(m, w, Pb, B, depth + 1)) return false;
  out.clear();
  for (int y : A) out.push_back(2 * y - 1);
  for (int i = (int)B.size() - 1; i >= 0; i--) out.push_back(2 * B[i]);
  return true;
}
static bool solve(int n, int nu, PS P, vector<int>& out, int depth) {
  nu %= n; canon(P);
  string kk = key(n, nu, P);
  auto it = memo.find(kk);
  if (it != memo.end()) { out = it->second.ord; return it->second.ok; }
  memo[kk] = {false, {}}; // guard against cycles
  bool ok = false; vector<int> res;
  // cycle check is left to the base solver / failure
  if (n == 1) { ok = true; res = {1}; }
  else if (n <= BASE) ok = baseSolve(n, nu, P, res);
  else {
    // candidate (n', nu', transform) list
    int nus[2] = {nu, (n - nu) % n}; int nmir = (n % 2 == 1 && nu % 2 == 1) ? 2 : 1;
    for (int mi = 0; mi < 2 && !ok; mi++) {
      if (mi == 1 && !MIRALL && nmir == 1) break;
      int nv = nus[mi];
      PS Pm = P; if (mi) for (auto& e : Pm) e = {n + 1 - e.first, n + 1 - e.second};
      for (int v = 0; v < 4 && !ok; v++) {
        PS Q = Pm;
        if (v & 1) for (auto& e : Q) e = {sg(n, nv, e.first), sg(n, nv, e.second)};
        if (v & 2) for (auto& e : Q) swap(e.first, e.second);
        canon(Q);
        vector<int> o;
        if (decompose(n, nv, Q, o, depth)) {
          // undo: o = rev?( sig?( mirror?(pi) ) )
          if (v & 2) reverse(o.begin(), o.end());
          if (v & 1) for (auto& t : o) t = sg(n, nv, t);
          if (mi) for (auto& t : o) t = n + 1 - t;
          res = o; ok = true;
        }
      }
    }
    if (!ok && n % 2 == 1 && (nu == 1 || nu == n - 1) && n <= BASE2) ok = baseSolve(n, nu, P, res);
  }
  if (ok && !checkGood(n, nu, res, P)) { fprintf(stderr, "VERIFY FAIL %s\n", kk.c_str()); exit(1); }
  memo[kk] = {ok, res};
  if (!ok) { nfail++; if (VERB) fprintf(stderr, "fail %s\n", kk.c_str()); }
  out = res; return ok;
}
int main(int argc, char** argv) {
  int lo = atoi(argv[1]), hi = atoi(argv[2]), K = atoi(argv[3]);
  if (argc > 4) BASE = atoi(argv[4]);
  if (argc > 5) BASE2 = atoi(argv[5]);
  if (argc > 6) VERB = atoi(argv[6]);
  if (argc > 7) PALIN = atoi(argv[7]);
  if (argc > 8) MIRALL = atoi(argv[8]);
  long tot = 0, good = 0;
  for (int q = lo; q <= hi; q++) {
    string bad;
    for (int r = 1; K * r < q; r++) {
      vector<int> o; tot++;
      if (solve(q, r, {}, o, 0)) good++; else bad += " " + to_string(r);
    }
    if (!bad.empty()) printf("q=%d FAIL rho:%s\n", q, bad.c_str());
  }
  printf("total %ld ok %ld  memo %zu  budget-outs %ld\n", tot, good, memo.size(), nbudget);
}

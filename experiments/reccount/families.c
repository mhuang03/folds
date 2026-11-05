/* families.c: brute-force sizes of recursively constructible subfamilies of the
   semi-symmetric sequences, N = 1..NMAX (default 14).

   Every valid sequence w of [N] is enumerated (DFS) and tested against the rules of each
   family F; parts are "standardised" (increasing enumeration of their panel set -> 1..n)
   and looked up in F(n), n < N (stored as sorted arrays of 4-bit-packed permutations).

   rules
     P  parity blocks: the first (N+c)/2 panels form the parity class c, both parts in F
     C  q | N, 2 < q < N: N/q-blocks, each a full residue class mod q; the class order pi
        (class s -> panel s of the q-strip) is in F(q); every block in F(N/q)
     H  2 < q <= N/2, any q: blocks = full residue classes mod q in any order (w valid),
        every block in F(size)
     T  neutral split: some cut t (1 <= t < N) whose prefix set is neutral (balanced around
        every panel), both parts in F
     G  general split: some cut t, both standardised parts in F
   families   R1 = {P}, R2 = {P,C}, R2c = {P,C,H}, R3 = {P,C,H,T}, R4 = {P,C,H,T,G}
   one-level  U1 = {P,H,T} and G1 = {G} with "part in F" replaced by "part valid"
              (U1 = sequences with an exact product block structure at the top level;
               G1 = sequences with some cut whose two standardised parts are both valid)
   (base F(1) = {[1]}).  Output: N a(N) |R1| |R2| |R2c| |R3| |R4| |U1| |G1|.
   Optional argv[2] = family index to dump the R-family sets (not used by default). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#define NF 7
#define MAXN 16
typedef struct { uint64_t *v; long n, cap; } Set;
static Set fam[NF][MAXN + 1];
static int N;
static uint64_t Lm[MAXN + 2], Rm[MAXN + 2];
static uint8_t *neutral;
static int w[MAXN];
static long cnt[NF], total;
static const int rules[NF] = { 1, 1 | 2, 1 | 2 | 4, 1 | 2 | 4 | 8, 1 | 2 | 4 | 8 | 16,
                                1 | 4 | 8, 16 };
/* families 5, 6 are ONE-LEVEL: parts only need to be valid (any valid inner order) */
static uint64_t SL[MAXN + 1][MAXN + 2], SR[MAXN + 1][MAXN + 2];
static int validstd(int a, int b) {
  int n = b - a; uint64_t mask = 0, S = 0;
  for (int i = a; i < b; i++) mask |= 1ULL << (w[i] - 1);
  for (int i = a; i < b; i++) {
    int r = __builtin_popcountll(mask & ((1ULL << (w[i] - 1)) - 1)) + 1;
    if (__builtin_popcountll(S & SL[n][r]) != __builtin_popcountll(S & SR[n][r])) return 0;
    S |= 1ULL << (r - 1);
  }
  return 1;
}

static void push(Set *s, uint64_t x) {
  if (s->n == s->cap) { s->cap = s->cap ? 2 * s->cap : 1024; s->v = realloc(s->v, s->cap * 8); }
  s->v[s->n++] = x;
}
static int cmpu(const void *a, const void *b) {
  uint64_t x = *(uint64_t *)a, y = *(uint64_t *)b; return x < y ? -1 : x > y;
}
static int has(Set *s, uint64_t x) {
  long lo = 0, hi = s->n - 1;
  while (lo <= hi) { long m = (lo + hi) / 2; if (s->v[m] == x) return 1; if (s->v[m] < x) lo = m + 1; else hi = m - 1; }
  return 0;
}
/* standardise w[a..b) : code of the rank sequence */
static uint64_t stdcode(int a, int b) {
  uint64_t mask = 0, code = 0;
  for (int i = a; i < b; i++) mask |= 1ULL << (w[i] - 1);
  for (int i = a; i < b; i++) {
    uint64_t r = __builtin_popcountll(mask & ((1ULL << (w[i] - 1)) - 1));
    code |= r << (4 * (i - a));
  }
  return code;
}
static int inF(int f, int a, int b) { if (f >= 5) return validstd(a, b); return has(&fam[f][b - a], stdcode(a, b)); }

static int ruleP(int f) {
  for (int c = 0; c <= 1; c++) {
    int k = (N + c) / 2, ok = 1;
    for (int i = 0; i < k && ok; i++) if ((w[i] + c) % 2) ok = 0;
    if (ok && inF(f, 0, k) && inF(f, k, N)) return 1;
  }
  return 0;
}
static int ruleC(int f) {
  for (int q = 3; q < N; q++) {
    if (N % q) continue;
    int n = N / q, ok = 1; uint64_t pc = 0;
    for (int i = 0; i < q && ok; i++) {
      int s = w[i * n] % q;
      for (int j = 1; j < n; j++) if (w[i * n + j] % q != s) { ok = 0; break; }
      if (!ok) break;
      int panel = s == 0 ? q : s;
      pc |= (uint64_t)(panel - 1) << (4 * i);
      if (!inF(f, i * n, (i + 1) * n)) ok = 0;
    }
    if (ok && has(&fam[f][q], pc)) return 1;
  }
  return 0;
}
static int ruleH(int f) {
  for (int q = 3; 2 * q <= N; q++) {
    int pos = 0, ok = 1;
    while (pos < N && ok) {
      int s = w[pos] % q, sz = 0;
      for (int x = (s == 0 ? q : s); x <= N; x += q) sz++;
      for (int j = 0; j < sz; j++) if (w[pos + j] % q != s) { ok = 0; break; }
      if (ok && !inF(f, pos, pos + sz)) ok = 0;
      pos += sz;
    }
    if (ok) return 1;
  }
  return 0;
}
static int ruleT(int f) {
  uint64_t S = 0;
  for (int t = 1; t < N; t++) {
    S |= 1ULL << (w[t - 1] - 1);
    if (neutral[S] && inF(f, 0, t) && inF(f, t, N)) return 1;
  }
  return 0;
}
static int ruleG(int f) {
  for (int t = 1; t < N; t++) if (inF(f, 0, t) && inF(f, t, N)) return 1;
  return 0;
}
static void test(void) {
  total++;
  uint64_t code = 0;
  for (int i = 0; i < N; i++) code |= (uint64_t)(w[i] - 1) << (4 * i);
  for (int f = 0; f < NF; f++) {
    int r = rules[f], in = 0;
    if (N == 1) in = 1;
    else if ((r & 1) && ruleP(f)) in = 1;
    else if ((r & 2) && ruleC(f)) in = 1;
    else if ((r & 4) && ruleH(f)) in = 1;
    else if ((r & 8) && ruleT(f)) in = 1;
    else if ((r & 16) && ruleG(f)) in = 1;
    if (in) { cnt[f]++; if (f < 5) push(&fam[f][N], code); }
  }
}
static void dfs(int k, uint64_t S) {
  if (k == N) { test(); return; }
  for (int m = 1; m <= N; m++) {
    uint64_t b = 1ULL << (m - 1);
    if (S & b) continue;
    if (__builtin_popcountll(S & Lm[m]) != __builtin_popcountll(S & Rm[m])) continue;
    w[k] = m; dfs(k + 1, S | b);
  }
}
int main(int argc, char **argv) {
  int NMAX = argc > 1 ? atoi(argv[1]) : 14;
  printf("N a R1 R2 R2c R3 R4 U1 G1\n");
  for (int n = 1; n <= MAXN; n++) for (int m = 1; m <= n; m++) {
    int D = m - 1 < n - m ? m - 1 : n - m; SL[n][m] = SR[n][m] = 0;
    for (int d = 1; d <= D; d++) { SL[n][m] |= 1ULL << (m - d - 1); SR[n][m] |= 1ULL << (m + d - 1); } }
  for (N = 1; N <= NMAX; N++) {
    for (int m = 1; m <= N; m++) {
      int D = m - 1 < N - m ? m - 1 : N - m; Lm[m] = Rm[m] = 0;
      for (int d = 1; d <= D; d++) { Lm[m] |= 1ULL << (m - d - 1); Rm[m] |= 1ULL << (m + d - 1); }
    }
    neutral = calloc(1ULL << N, 1);
    for (uint64_t S = 1; S < (1ULL << N); S++) {
      int ok = 1;
      for (int m = 1; m <= N && ok; m++) if (__builtin_popcountll(S & Lm[m]) != __builtin_popcountll(S & Rm[m])) ok = 0;
      neutral[S] = ok;
    }
    total = 0; memset(cnt, 0, sizeof cnt);
    dfs(0, 0);
    for (int f = 0; f < 5; f++) qsort(fam[f][N].v, fam[f][N].n, 8, cmpu);
    printf("%d %ld", N, total);
    for (int f = 0; f < NF; f++) printf(" %ld", cnt[f]);
    printf("\n"); fflush(stdout);
    free(neutral);
  }
  return 0;
}

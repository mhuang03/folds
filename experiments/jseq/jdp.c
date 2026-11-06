/* jdp.c: full layered subset DP for g(S) (valid orderings of S from scratch), with
   g(X^c) collected for every window copy X of [N].

   usage: jdp N MOD [threads] > out
     MOD = 0     : u64 words, arithmetic mod 2^64 (wrap-around)
     MOD = p     : arithmetic mod p (p < 2^63); words of 1, 2, 4 or 8 bytes by the size of p
   Output lines:
     "copy k maskhex gcomp"   g([N] \ X) mod MOD for each copy X (|X| = k, 1 <= k <= N-1)
     "gcopy k maskhex g"      g(X) mod MOD (should be a(k))
     "C k value"              C_N(k) = sum of g(X^c) over copies of size k (mod MOD)
     "a value"                g([N]) = a(N) mod MOD
   Layers are colex-ranked k-subsets (bit m-1 = panel m); only two layers are held.
   Memory: 2 * C(N, N/2) words.  Validity of adding p to S = T \ p is tested on T
   (p itself lies in neither arm). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>

typedef unsigned __int128 u128;
static int N;
static uint64_t MOD; /* 0 = 2^64 */
static int WB;       /* bytes per stored word: 1, 2, 4 or 8 */
static uint64_t Lm[64], Rm[64];
static uint64_t Cb[65][65];

/* ---- copies (DFS from copies.c) ---- */
static int cs, P[130], x[130], req[130];
static uint64_t *cmask; static int ncm, capm;
static void dfs(int t) {
  if (t > N) {
    if (P[N] == cs) {
      uint64_t m = 0;
      for (int i = 1; i <= N; i++) if (x[i]) m |= 1ULL << (i - 1);
      if (ncm == capm) { capm = capm ? 2 * capm : 1024; cmask = realloc(cmask, capm * 8); }
      cmask[ncm++] = m;
    }
    return;
  }
  for (int v = 0; v <= 1; v++) {
    x[t] = v; P[t] = P[t - 1] + v;
    if (P[t] > cs || P[t] + (N - t) < cs) continue;
    if (req[t] >= 0 && req[t] != P[t]) continue;
    int ok = 1, setreq = -1;
    if (v) {
      int m = t;
      if (2 * m - 1 <= N) {
        int T = P[m - 1] + P[m], tt = 2 * m - 1;
        if (tt == m) {}
        else if (req[tt] >= 0 && req[tt] != T) ok = 0;
        else if (T < P[t] || T > P[t] + (tt - t)) ok = 0;
        else if (req[tt] < 0) setreq = tt;
      } else if (P[m - 1] - P[2 * m - 1 - N] != cs - P[m]) ok = 0;
    }
    if (!ok) continue;
    int bad = 0;
    for (int u = t + 1; u <= N; u++)
      if (req[u] >= 0 && (req[u] < P[t] || req[u] > P[t] + (u - t))) { bad = 1; break; }
    if (bad) continue;
    if (setreq >= 0) req[setreq] = P[t - 1] + P[t];
    dfs(t + 1);
    if (setreq >= 0) req[setreq] = -1;
  }
}
static int isCopy(uint64_t S) {
  for (uint64_t r = S; r; r &= r - 1) {
    int p = __builtin_ctzll(r);
    if (__builtin_popcountll(S & Lm[p]) != __builtin_popcountll(S & Rm[p])) return 0;
  }
  return 1;
}

static uint64_t rankS(uint64_t S) {
  uint64_t r = 0; int i = 0;
  for (; S; S &= S - 1, i++) r += Cb[__builtin_ctzll(S)][i + 1];
  return r;
}
static uint64_t unrank(uint64_t r, int k) { /* colex */
  uint64_t S = 0;
  for (int i = k; i >= 1; i--) {
    int c = i - 1;
    while (Cb[c + 1][i] <= r) c++;
    r -= Cb[c][i];
    S |= 1ULL << c;
  }
  return S;
}
static inline uint64_t nextComb(uint64_t v) {
  uint64_t t = v | (v - 1);
  return (t + 1) | (((~t & -~t) - 1) >> (__builtin_ctzll(v) + 1));
}

static void *prev, *cur;
static inline uint64_t getv(void *a, uint64_t i) {
  switch (WB) { case 1: return ((uint8_t *)a)[i]; case 2: return ((uint16_t *)a)[i];
                case 4: return ((uint32_t *)a)[i]; default: return ((uint64_t *)a)[i]; }
}
static inline void setv(void *a, uint64_t i, uint64_t v) {
  switch (WB) { case 1: ((uint8_t *)a)[i] = (uint8_t)v; break; case 2: ((uint16_t *)a)[i] = (uint16_t)v; break;
                case 4: ((uint32_t *)a)[i] = (uint32_t)v; break; default: ((uint64_t *)a)[i] = v; }
}
static inline uint64_t addm(uint64_t a, uint64_t b) {
  if (!MOD) return a + b;
  uint64_t s = a + b; /* a, b < MOD < 2^63 */
  return s >= MOD ? s - MOD : s;
}

int main(int argc, char **argv) {
  N = atoi(argv[1]); MOD = strtoull(argv[2], 0, 10);
  int th = argc > 3 ? atoi(argv[3]) : 3;
  omp_set_num_threads(th);
  WB = !MOD ? 8 : MOD < 256 ? 1 : MOD < 65536 ? 2 : MOD < (1ULL << 32) ? 4 : 8;
  int W32 = WB < 8;
  if (MOD >= (1ULL << 63)) { fprintf(stderr, "MOD too big\n"); return 1; }
  for (int n = 0; n <= 64; n++) { Cb[n][0] = 1; for (int k = 1; k <= 64; k++) Cb[n][k] = n ? Cb[n - 1][k - 1] + Cb[n - 1][k] : 0; }
  for (int p = 0; p < N; p++) {
    int m = p + 1, D = m - 1 < N - m ? m - 1 : N - m; Lm[p] = Rm[p] = 0;
    for (int d = 1; d <= D; d++) { Lm[p] |= 1ULL << (p - d); Rm[p] |= 1ULL << (p + d); }
  }
  for (cs = 1; cs < N; cs++) { for (int i = 0; i < 130; i++) req[i] = -1; P[0] = 0; dfs(1); }
  for (int i = 0; i < ncm; i++) if (!isCopy(cmask[i])) { fprintf(stderr, "bad copy\n"); return 1; }
  fprintf(stderr, "N=%d copies=%d\n", N, ncm);
  uint64_t full = (N == 64) ? ~0ULL : (1ULL << N) - 1;
  uint64_t maxC = Cb[N][N / 2];
  size_t wb = WB;
  prev = malloc(maxC * wb); cur = malloc(maxC * wb);
  if (!prev || !cur) { fprintf(stderr, "alloc\n"); return 1; }
  setv(prev, 0, 1);
  uint64_t *res = calloc(ncm, 8), *resg = calloc(ncm, 8);
  for (int k = 1; k <= N; k++) {
    uint64_t tot = Cb[N][k];
    int nch = th * 64; if ((uint64_t)nch > tot) nch = (int)tot;
#pragma omp parallel for schedule(dynamic, 1)
    for (int c = 0; c < nch; c++) {
      uint64_t r0 = tot * c / nch, r1 = tot * (c + 1) / nch;
      if (r0 >= r1) continue;
      uint64_t T = unrank(r0, k);
      int pos[64]; uint64_t A[65], B[65];
      for (uint64_t r = r0; r < r1; r++, T = (r < r1 ? nextComb(T) : T)) {
        int n = 0; for (uint64_t s = T; s; s &= s - 1) pos[n++] = __builtin_ctzll(s);
        A[0] = 0; for (int i = 0; i < n; i++) A[i + 1] = A[i] + Cb[pos[i]][i + 1];
        B[n] = 0; for (int i = n - 1; i >= 0; i--) B[i] = B[i + 1] + (i ? Cb[pos[i]][i] : 0);
        uint64_t acc = 0; u128 acc128 = 0;
        for (int j = 0; j < n; j++) {
          int p = pos[j];
          if (__builtin_popcountll(T & Lm[p]) != __builtin_popcountll(T & Rm[p])) continue;
          uint64_t idx = A[j] + B[j + 1];
          uint64_t v = getv(prev, idx);
          if (W32 || !MOD) acc += v; else acc = addm(acc, v);
        }
        (void)acc128;
        if (W32) acc %= MOD;
        setv(cur, r, acc);
      }
    }
    /* collect */
    for (int i = 0; i < ncm; i++) {
      uint64_t X = cmask[i]; int kx = __builtin_popcountll(X);
      if (N - kx == k) res[i] = getv(cur, rankS(full & ~X));
      if (kx == k) resg[i] = getv(cur, rankS(X));
    }
    void *t = prev; prev = cur; cur = t;
    fprintf(stderr, "layer %d done\n", k);
  }
  uint64_t a = getv(prev, 0);
  uint64_t Csum[65] = {0};
  for (int i = 0; i < ncm; i++) {
    int kx = __builtin_popcountll(cmask[i]);
    printf("copy %d %llx %llu\n", kx, (unsigned long long)cmask[i], (unsigned long long)res[i]);
    printf("gcopy %d %llx %llu\n", kx, (unsigned long long)cmask[i], (unsigned long long)resg[i]);
    Csum[kx] = MOD ? (uint64_t)(((u128)Csum[kx] + res[i]) % MOD) : Csum[kx] + res[i];
  }
  for (int k = 1; k < N; k++) printf("C %d %llu\n", k, (unsigned long long)Csum[k]);
  printf("a %llu\n", (unsigned long long)a);
  return 0;
}

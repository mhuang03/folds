/* cover7.c N1 N2 [rules]: check the covering statement `Live7.CoverLemma7 E7` for N1 <= N <= N2.
   For every pair 1 <= u < v <= N that is not dead, decide whether Settled7 N u v or
   Settled7 N (N+1-v) (N+1-u) holds (faithful to Folds/Live6.lean `Settled` + Folds/Live7.lean
   `SettledZ`), searching the witnesses directly:
     inward    v <= 2u + 1 or 2v <= N + u + 2
     one       u = 1, v = N, N odd, N != 7
     beatty    X(N, p, h) = {floor((rN - h)/p)}, h <= 1, h + 2p <= N + 1, non-dead preimage
     swap      X(N, p, h) with the last element moved to N - c (p >= 3 odd, h <= 1, c >= 2,
               2cp + 1 <= N + h), non-dead preimage
     chiY      N = 0 mod 4, N >= 8: chiY(1) = 1, chiY(y) = 2y on [N/2]
     dbl       N = (2j+1) n, j >= 1: oddRes j on [(j+1) n], evenRes j on [j n]
     z         Z(N, p) = {floor(k(N+2)/(p+1))}, 1 <= p, 2p <= N
   Pairs neither settled nor in E7 (the hard core list for N <= 128, file core128.txt) are printed.
   rules: a string of letters (i=inward o=one b=beatty s=swap y=chiY d=dbl z=z), default all.
   Prints per N the number of failures, and the failures. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef long long ll;
static int N;
static const char *rules = "iobsydz";
static int has(char c) { return strchr(rules, c) != NULL; }

static int dead(int n, int a, int b) { return a == 1 && b == n && ((n % 2 == 0 && n >= 4) || n == 7); }

/* index of x in X(N, p, h) (1..p) or 0 */
static int bidx(int p, int h, int x) {
  if (x < 1 || x > N) return 0;
  ll t = (ll)p * (x + 1) + h - 1;
  if (t % N <= p - 1) return (int)(t / N);
  return 0;
}
/* index of x in Z(N, p) or 0 */
static int zidx(int p, int x) {
  if (x < 1 || x > N) return 0;
  ll M = N + 2, q = p + 1;
  ll r = ((-(q * x)) % M + M) % M;
  if (r <= q - 1) return (int)((q * x + r) / M);
  return 0;
}

static int direct(int u, int v) {  /* Settled7 N u v, u < v */
  if (has('i') && (v <= 2 * u + 1 || 2 * v <= N + u + 2)) return 1;
  if (has('o') && u == 1 && v == N && N % 2 == 1 && N != 7) return 1;
  if (has('b'))
    for (int p = 1; 2 * p <= N + 1; p++)
      for (int h = 0; h <= 1; h++) {
        if (h + 2 * p > N + 1) continue;
        int a = bidx(p, h, u), b = bidx(p, h, v);
        if (a && b && a < b && !dead(p, a, b)) return 1;
      }
  if (has('z'))
    for (int p = 1; 2 * p <= N; p++) {
      int a = zidx(p, u), b = zidx(p, v);
      if (a && b && a < b && !dead(p, a, b)) return 1;
    }
  if (has('s'))
    for (int p = 3; p <= N; p += 2)
      for (int h = 0; h <= 1; h++)
        for (int c = 2; 2 * c * p + 1 <= N + h; c++) {
          /* swapF: r < p -> beatty, r = p -> N - c */
          if (v != N - c) continue;
          int a = bidx(p, h, u);
          if (a && a < p && !dead(p, a, p)) return 1;
        }
  if (has('y') && N % 4 == 0 && N >= 8) {
    int n = N / 2, a, b;
    a = (u == 1) ? 1 : (u % 2 == 0 && u >= 4 ? u / 2 : 0);
    b = (v == 1) ? 1 : (v % 2 == 0 && v >= 4 ? v / 2 : 0);
    if (a && b && a < b && b <= n && !dead(n, a, b)) return 1;
  }
  if (has('d'))
    for (int j = 1; 2 * j + 1 <= N; j++) {
      int d = 2 * j + 1;
      if (N % d) continue;
      int n = N / d;
      /* oddRes j y = d*((y-1)/(j+1)) + 2*((y-1)%(j+1)) + 1, y in [1, (j+1) n] */
      int ru = (u - 1) % d, rv = (v - 1) % d;
      if (ru % 2 == 0 && rv % 2 == 0) {
        int a = (j + 1) * ((u - 1) / d) + ru / 2 + 1, b = (j + 1) * ((v - 1) / d) + rv / 2 + 1;
        int m = (j + 1) * n;
        if (a < b && b <= m && !dead(m, a, b)) return 1;
      }
      /* evenRes j y = d*((y-1)/j) + 2*((y-1)%j) + 2, y in [1, j n] */
      if (u >= 2 && v >= 2) {
        int su = (u - 2) % d, sv = (v - 2) % d;
        if (su % 2 == 0 && su <= 2 * j - 2 && sv % 2 == 0 && sv <= 2 * j - 2) {
          int a = j * ((u - 2) / d) + su / 2 + 1, b = j * ((v - 2) / d) + sv / 2 + 1;
          int m = j * n;
          if (a < b && b <= m && !dead(m, a, b)) return 1;
        }
      }
    }
  return 0;
}

static int core[2000][3], ncore = 0;
static int inCore(int n, int u, int v) {
  for (int i = 0; i < ncore; i++)
    if (core[i][0] == n && ((core[i][1] == u && core[i][2] == v) ||
                            (core[i][1] == n + 1 - v && core[i][2] == n + 1 - u)))
      return 1;
  return 0;
}

int main(int argc, char **argv) {
  int N1 = atoi(argv[1]), N2 = atoi(argv[2]);
  if (argc > 3) rules = argv[3];
  FILE *f = fopen("core128.txt", "r");
  if (f) {
    int a, b, c;
    while (fscanf(f, "%d %d %d", &a, &b, &c) == 3) { core[ncore][0] = a; core[ncore][1] = b; core[ncore][2] = c; ncore++; }
    fclose(f);
  }
  long total = 0;
  for (N = N1; N <= N2; N++) {
    int fails = 0;
    for (int u = 1; u <= N; u++)
      for (int v = u + 1; v <= N; v++) {
        if (u > N + 1 - v) continue;  /* the statement is mirror-symmetric */
        if (dead(N, u, v)) continue;
        if (direct(u, v) || direct(N + 1 - v, N + 1 - u)) continue;
        if (inCore(N, u, v)) continue;
        if (fails < 20) printf("  FAIL %d (%d, %d)\n", N, u, v);
        fails++;
      }
    total += fails;
    printf("%d %d\n", N, fails);
    fflush(stdout);
  }
  printf("total failures %ld\n", total);
  return 0;
}

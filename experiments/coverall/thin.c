/* thin.c N1 N2 STEP : the thin sets (Lean `Thin`), restricted to mixed-parity non-special pairs
   outside the old regions; which edge certificates (key conditions, keys.h) cover them.
   Candidates: family Z/X0/X1, orientation (u',u) [o=1] or (u,u') [o=0], w1 = (p, q), edge 4/1.
   Prints per class (diag d, estrip e, cluster, u<=3) the counts left after the candidates. */
#include "keys.h"
typedef struct { int f, o; ll p, q; int e; } KC;
static KC kc[] = {
  {0,1,1,1,4},{0,1,2,1,4},{0,1,2,1,1},{1,1,1,1,4},{1,1,2,1,4},{1,1,2,1,1},{2,1,1,1,4},{2,1,2,1,4},{2,1,2,1,1},
  {0,1,3,2,4},{0,1,3,2,1},{1,1,3,2,4},{1,1,3,2,1},{0,1,1,1,1},{1,1,1,1,1},
  {0,0,1,1,4},{0,0,1,1,1},{1,0,1,1,4},{1,0,1,1,1},{0,1,3,1,4},{0,1,3,1,1},{1,1,3,1,1},{1,1,3,1,4},
  {0,1,4,3,4},{0,1,4,3,1},{1,1,4,3,4},{1,1,4,3,1},{0,1,5,3,1},{0,1,5,3,4},{1,1,5,3,1},{1,1,5,3,4}};
#define NK ((int)(sizeof kc / sizeof kc[0]))
static int testK(ll N, ll u, ll up, KC k) {
  ll x = k.o ? up : u, y = k.o ? u : up;
  if (k.f > 0 && y < 3) return 0;
  Fam f = k.f == 0 ? famZo(N, x, y) : k.f == 1 ? famX0o(N, x, y) : famX1o(N, x, y);
  return k.e == 4 ? edge4Keys(f, k.p, k.q) : edge1Keys(f, k.p, k.q);
}
static int thinClass(ll N, ll u, ll v, ll *off) {
  if (u <= 3) { *off = u; return 0; }
  if (v <= u + 9) { *off = v - u; return 1; }
  if (2 * u <= v + 12 && v <= 2 * u + 15 && N <= 8 * u + 320) { *off = v - 2 * u; return 2; }
  if (N <= 4 * u + 80 && 4 * u <= N + 40 && N <= u + 2 * v + 81) { *off = 0; return 3; }
  return -1;
}
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]), STEP = atoll(argv[3]);
  int verbose = argc > 4;
  static ll tot[4][64], left[4][64], byk[NK];
  for (ll N = N1; N <= N2; N += STEP)
    for (ll u = 2; 3 * u + 1 <= N; u++)
      for (ll v = u; u + 2 * v <= N - 1; v++) {
        if (!isPair(N, u, v)) continue;
        ll off; int c = thinClass(N, u, v, &off);
        if (c < 0) continue;
        if (provenOld(N, u, v)) continue;
        int oi = (int)(off + 20);
        tot[c][oi]++;
        int k;
        for (k = 0; k < NK; k++) if (testK(N, u, v, kc[k])) break;
        if (k < NK) { byk[k]++; continue; }
        left[c][oi]++;
        if (verbose) printf("left c=%d off=%lld N=%lld u=%lld v=%lld  u-N/4=%lld delta=%lld 8u-N=%lld\n", c, off, N, u, v, u - N / 4, N - 1 - u - 2 * v, 8 * u - N);
      }
  const char *nm[4] = {"u<=3", "diag d", "estrip e", "cluster"};
  for (int c = 0; c < 4; c++) {
    printf("%s:", nm[c]);
    for (int i = 0; i < 64; i++) if (tot[c][i]) printf(" %d:%lld/%lld", i - 20, left[c][i], tot[c][i]);
    printf("\n");
  }
  for (int k = 0; k < NK; k++) if (byk[k]) printf(" k%d(f%d o%d %lld,%lld e%d):%lld", k, kc[k].f, kc[k].o, kc[k].p, kc[k].q, kc[k].e, byk[k]);
  printf("\n");
  return 0;
}

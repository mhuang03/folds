/* wit.c N u u' [all]: list s-witnesses (faithful to dirOK, s >= R) of the pair (u, v = N+1-u').
   combo: o = orientation (0: x = u, y = u'; 1: x = u', y = u), f = Z / X0 / X1.
   Witness: s in [max(R,2), smax], a = ceil((sx+al)/K) with aK - sx - al in [0, s-1], a >= amin,
   c with cK - sR - be in [0, s-1].  Prints s, a, c, X = aK - sx - al, Y = cK - sR - be. */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
static int cnt = 0, lim = 1000;
static void combo(const char *nm, ll K, ll x, ll R, ll al, ll be, ll smax, ll amin) {
  ll lo = R > 2 ? R : 2;
  for (ll s = lo; s <= smax; s++) {
    ll a = (s * x + al + K - 1) / K, X = a * K - s * x - al;
    if (X > s - 1 || a < amin) continue;
    ll c = (s * R + be + K - 1) / K, Y = c * K - s * R - be;
    if (Y > s - 1) continue;
    if (cnt++ < lim) printf("%s s=%lld a=%lld c=%lld X=%lld Y=%lld\n", nm, s, a, c, X, Y);
  }
}
int main(int argc, char **argv) {
  ll N = atoll(argv[1]), u = atoll(argv[2]), up = atoll(argv[3]);
  if (argc > 4) lim = atoi(argv[4]);
  ll M = N + 2;
  for (int o = 0; o < 2; o++) {
    ll x = o ? up : u, y = o ? u : up;
    char b[3][16];
    sprintf(b[0], "%dZ ", o); sprintf(b[1], "%dX0", o); sprintf(b[2], "%dX1", o);
    combo(b[0], M, x, y, 0, 1, M / 2, 2);
    combo(b[1], N, x, y - 2, 0, 1, (N + 1) / 2, 1);
    combo(b[2], N, x, y - 2, 1, 0, N / 2, 2);
  }
  printf("total %d\n", cnt);
  return 0;
}

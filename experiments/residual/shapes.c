/* shapes.c u u' par [NMAX]: a uniform witness for the fixed shape (u, u') for all N >= 301 with
   N = par (mod 2) (N <= NMAX checked): orientation o, family f, constants a, c and
   s = floor(num K / den) (K = N + 2 for Z, N for X).  Prints the first few that work. */
#include "common.h"
static int okWit(ll K, ll x, ll R, ll al, ll be, ll smax, ll amin, ll a, ll c, ll s) {
  if (a < amin || s < 2 || s < R || s > smax) return 0;
  if (s * x + al > a * K || a * K + 1 > s * (x + 1) + al) return 0;
  if (s * R + be > c * K || c * K + 1 > s * R + be + s) return 0;
  return 1;
}
int main(int argc, char **argv) {
  ll u = atoll(argv[1]), up = atoll(argv[2]), par = atoll(argv[3]);
  ll NMAX = argc > 4 ? atoll(argv[4]) : 20000;
  int found = 0;
  for (int o = 1; o >= 0 && found < 6; o--) {
    ll x = o ? up : u, y = o ? u : up;
    for (int f = 0; f < 3 && found < 6; f++) {
      if (f > 0 && y < 2) continue;
      for (ll a = 1; a <= 8; a++)
        for (ll c = 1; c <= 8; c++)
          for (ll den = 1; den <= 60; den++)
            for (ll num = 1; 2 * num <= den; num++) {
              int good = 1;
              for (ll N = 301 + ((301 % 2) != par); N <= NMAX && good; N += 2) {
                ll K, R, al, be, smax, amin;
                comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
                ll s = num * K / den;
                if (!okWit(K, x, R, al, be, smax, amin, a, c, s)) good = 0;
              }
              if (good) {
                printf("shape (%lld,%lld) N%%2=%lld: o=%d f=%d a=%lld c=%lld s=%lld*K/%lld\n", u, up, par, o, f, a, c, num, den);
                found++;
                goto next;
              }
            }
    next:;
    }
  }
  if (!found) printf("shape (%lld,%lld) N%%2=%lld: none\n", u, up, par);
  return 0;
}

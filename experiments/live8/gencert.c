/* gencert.c N1 N2 [file]: certificates for Live8.mixedB.  For every N, every u >= 1 with a
   wide pair, and every v in [vLo, N + 1 - u] with u + v odd, a certificate c = 8 p + 2 f + o
   (o = orientation, f = family 0: X(N,p,0), 1: X(N,p,1), 2: Z(N,p), 3: fallback search),
   c = 0 for the dead pair.  The certificates of one u are packed into one number in base 2^12
   (first v = least significant).  Output: one Lean theorem per N.
   Faithful to Live8.beattyW / zW (candidate indices candB, candZ of Live7). */
#include <stdio.h>
#include <stdlib.h>
typedef long long ll;
typedef unsigned __int128 u128;

static int deadB(ll n, ll a, ll b) { return a == 1 && b == n && ((n % 2 == 0 && 4 <= n) || n == 7); }
static ll candB(ll N, ll p, ll h, ll x) { return (p * (x + 1) + h - 1) / N; }
static ll candZ(ll N, ll p, ll x) { return ((p + 1) * x + N + 1) / (N + 2); }
static ll beatty(ll N, ll p, ll h, ll r) { ll t = r * N - h; if (t < 0) t = 0; return t / p; }
static ll zF(ll N, ll p, ll k) { return k * (N + 2) / (p + 1); }

static int beattyW(ll N, ll p, ll h, ll x, ll y) {
  if (p < 1 || h + 2 * p > N + 1) return 0;
  ll a = candB(N, p, h, x), b = candB(N, p, h, y);
  if (a < 1 || a >= b || b > p || deadB(p, a, b)) return 0;
  return beatty(N, p, h, a) == x && beatty(N, p, h, b) == y;
}
static int zW(ll N, ll p, ll x, ll y) {
  if (p < 1 || 2 * p > N) return 0;
  ll a = candZ(N, p, x), b = candZ(N, p, y);
  if (a < 1 || a >= b || b > p || deadB(p, a, b)) return 0;
  return zF(N, p, a) == x && zF(N, p, b) == y;
}

static ll cert(ll N, ll u, ll v) {
  if (deadB(N, u, v)) return 0;
  for (int o = 0; o < 2; o++) {
    ll x = o ? N + 1 - v : u, y = o ? N + 1 - u : v;
    for (ll p = N / 2 + 1; p >= 1; p--) {
      if (beattyW(N, p, 0, x, y)) return 8 * p + 0 + o;
      if (beattyW(N, p, 1, x, y)) return 8 * p + 2 + o;
      if (zW(N, p, x, y)) return 8 * p + 4 + o;
    }
  }
  return 6;
}

static void printBig(FILE *f, unsigned *dig, int n) {
  /* number = sum dig[i] 4096^i, print in decimal */
  if (n == 0) { fprintf(f, "0"); return; }
  /* convert base 4096 -> base 10^9 */
  int cap = n * 2 + 2;
  unsigned *out = calloc(cap, sizeof(unsigned));
  int len = 0;
  for (int i = n - 1; i >= 0; i--) {
    /* out = out * 4096 + dig[i] */
    unsigned long long carry = dig[i];
    for (int j = 0; j < len; j++) {
      unsigned long long t = (unsigned long long)out[j] * 4096ULL + carry;
      out[j] = t % 1000000000ULL;
      carry = t / 1000000000ULL;
    }
    while (carry) { out[len++] = carry % 1000000000ULL; carry /= 1000000000ULL; }
  }
  if (len == 0) { fprintf(f, "0"); free(out); return; }
  fprintf(f, "%u", out[len - 1]);
  for (int j = len - 2; j >= 0; j--) fprintf(f, "%09u", out[j]);
  free(out);
}

int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  FILE *f = stdout;
  long fallback = 0;
  for (ll N = N1; N <= N2; N++) {
    fprintf(f, "set_option maxHeartbeats 0 in\ntheorem mixedB_%lld : mixedB %lld\n    [", N, N);
    int first = 1;
    for (ll u = 1; 3 * u + 1 <= N; u++) {
      ll vlo = 2 * u + 2;
      if ((N + u + 4) / 2 > vlo) vlo = (N + u + 4) / 2;
      unsigned dig[20000];
      int n = 0;
      for (ll v = vlo; v <= N + 1 - u; v++) {
        if ((u + v) % 2 != 1) continue;
        ll c = cert(N, u, v);
        if (c >= 4096) { fprintf(stderr, "certificate too large\n"); return 1; }
        if ((c / 2) % 4 == 3) { fallback++; fprintf(stderr, "fallback N=%lld u=%lld v=%lld\n", N, u, v); }
        dig[n++] = (unsigned)c;
      }
      if (!first) fprintf(f, ", ");
      first = 0;
      printBig(f, dig, n);
    }
    fprintf(f, "] = true := by\n  decide +kernel\n\n");
  }
  fprintf(stderr, "fallbacks %ld\n", fallback);
  return 0;
}

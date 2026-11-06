/* rules.c N1 N2 T MMAX [umin]: block rules for the wide mixed pairs.
   A rule = (family F in {Z, X0, X1}, orientation o, slope m, blocks t, t2) with |t|, |t2| <= T.
   With (x, y) = (u, u') (o = 0) or (u', u) (o = 1), K = N + 2 (Z) or N (X), e = K - m s:
     X_h: left  t N <= x e - m h < t N + N - e,           t  = x     mod m
          right t2 N + e < (y - 1) e + m h < (t2 + 1) N,   t2 = y - 2 mod m
     Z:   left  t M <= x e < t M + M - e,                  t  = x     mod m
          right t2 M + e < (y + 1) e < (t2 + 1) M,         t2 = y     mod m
   plus the index constraints (a = (x - t)/m >= 1, c = (y - 2 - t2)/m >= 0 (X) or
   (y - t2)/m >= 1 (Z), a + c < s, non-dead preimage, copy constraints).
   Every rule found is re-checked by direct membership.  Prints the pairs covered by no rule
   (with u >= umin), and a histogram of the minimal T. */
#include <stdio.h>
#include <stdlib.h>

typedef long long ll;
#define FREE 99999
static ll G[8];
static ll VU = -1, VUP = -1;

static ll fdiv(ll a, ll b) { ll q = a / b; if ((a % b != 0) && ((a < 0) != (b < 0))) q--; return q; }
static ll fmod_(ll a, ll b) { ll r = a % b; if (r < 0) r += b; return r; }

static int dead(ll n, ll a, ll b) { return a == 1 && b == n && ((n % 2 == 0 && n >= 4) || n == 7); }

/* direct check: (x, y) with x from the left at index a, y from the right (v = N+1-y). */
static int checkX(ll N, ll p, ll h, ll a, ll b, ll x, ll y) {
  if (p < 1 || h + 2 * p > N + 1 || a < 1 || a >= b || b > p || dead(p, a, b)) return 0;
  if ((a * N - h) / p != x) return 0;
  if ((b * N - h) / p != N + 1 - y) return 0;
  return 1;
}
static int checkZ(ll N, ll p, ll a, ll b, ll x, ll y) {
  ll M = N + 2, q = p + 1;
  if (p < 1 || 2 * p > N || a < 1 || a >= b || b > p || dead(p, a, b)) return 0;
  if (a * M / q != x) return 0;
  if (b * M / q != N + 1 - y) return 0;
  return 1;
}

/* try a rule; returns 1 if some e works */
static int tryRule(ll N, int fam, ll x, ll y, ll m, ll t, ll t2) {
  /* fam: 0 = Z, 1 = X0, 2 = X1 */
  ll h = fam == 2 ? 1 : 0;
  ll K = fam == 0 ? N + 2 : N;
  if (fmod_(x - t, m) != 0) return 0;
  if (t2 != FREE) {
  if (fam == 0) { if (fmod_(y - t2, m) != 0) return 0; }
  else { if (fmod_(y - 2 - t2, m) != 0) return 0; } }
  ll a = (x - t) / m;
  ll c = t2 == FREE ? 0 : (fam == 0 ? (y - t2) / m : (y - 2 - t2) / m);
  if (a < 1) return 0;
  /* scan e near m t; e in [m*min(t,t2) - 3m, m*(max+1) + 3m] is enough when x,y large;
     to be safe scan a window */
  ll lo, hi;
  if (t2 == FREE) { lo = fdiv(t * K, x) - 2 * m; hi = fdiv((t + 1) * K, x) + 2 * m; }
  else { lo = m * (t < t2 ? t : t2) - 4 * m - 2; hi = m * ((t > t2 ? t : t2) + 1) + 4 * m + 2; }
  /* for small x, y the e-range is larger: widen */
  ll w = t2 == FREE ? 0 : 4 * m * (K / (x > 1 ? x : 1) + 2);
  if (w > 100000) w = 100000;
  lo -= w; hi += w;
  ll e0 = lo + fmod_(K - lo, m);
  for (ll e = e0; e <= hi; e += m) {
    ll s = (K - e) / m;
    if (s < 1) continue;
    if (fam == 0) {
      if (!(t * K <= x * e && x * e < t * K + K - e)) continue;
      ll tt2 = t2;
      if (t2 == FREE) { tt2 = fdiv((y + 1) * e, K); if (fmod_(y - tt2, m) != 0) continue; c = (y - tt2) / m; }
      if (!(tt2 * K + e < (y + 1) * e && (y + 1) * e < (tt2 + 1) * K)) continue;
      ll p = s - 1, b = s - c;
      if (checkZ(N, p, a, b, x, y)) { G[0]=0;G[1]=m;G[2]=t;G[3]=tt2;G[4]=e;G[5]=s;G[6]=a;G[7]=c; return 1; }
    } else {
      if (!(t * K <= x * e - m * h && x * e - m * h < t * K + K - e)) continue;
      ll ww = (y - 1) * e + m * h;
      ll tt2 = t2;
      if (t2 == FREE) { tt2 = fdiv(ww, K); if (fmod_(y - 2 - tt2, m) != 0) continue; c = (y - 2 - tt2) / m; }
      if (!(tt2 * K + e < ww && ww < (tt2 + 1) * K)) continue;
      ll p = s, b = s - c;
      if (checkX(N, p, h, a, b, x, y)) { G[0]=fam;G[1]=m;G[2]=t;G[3]=tt2;G[4]=e;G[5]=s;G[6]=a;G[7]=c; return 1; }
    }
  }
  return 0;
}

int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  int T = atoi(argv[3]), MMAX = atoi(argv[4]);
  ll umin = argc > 5 ? atoll(argv[5]) : 1;
  int colmode = argc > 6 ? atoi(argv[6]) : 0;
  if (argc > 8) { VU = atoll(argv[7]); VUP = atoll(argv[8]); }
  long hist[4096] = {0};
  long unc = 0;
  for (ll N = N1; N <= N2; N++) {
    for (ll u = umin; 3 * u + 1 <= N; u++)
      for (ll up = u; u + 2 * up <= N - 1; up++) {
        ll v = N + 1 - up;
        if ((u + v) % 2 == 0) continue;
        if (u == 1 && up == 1) continue;           /* dead (1, N) */
        if (u == 3 && up == 4) continue;           /* swap family (3, N - 3) */
        if (u == 1 && N % 4 == 0 && up == N / 2 - 1) continue; /* chiY (1, N/2 + 2) */
        int best = -1;
        for (int k = 0; k <= T && best < 0; k++) {
          for (int o = 0; o < 2 && best < 0; o++) {
            ll x = o ? up : u, y = o ? u : up;
            for (int fam = 0; fam < 3 && best < 0; fam++)
              for (ll m = 2; m <= MMAX && best < 0; m++)
                if (colmode) {
                  for (ll t = -k; t <= k && best < 0; t += (k ? 2 * k : 1))
                    if (tryRule(N, fam, x, y, m, t, FREE)) { best = k; if (u == VU && up == VUP) printf("pair %lld %lld: o=%d fam=%lld m=%lld t=%lld t2=%lld e=%lld s=%lld a=%lld c=%lld\n", u, up, o, G[0],G[1],G[2],G[3],G[4],G[5],G[6],G[7]); }
                } else
                for (ll t = -k; t <= k && best < 0; t++)
                  for (ll t2 = -k; t2 <= k && best < 0; t2++) {
                    if ((t > -k && t < k) && (t2 > -k && t2 < k)) continue; /* only new */
                    if (tryRule(N, fam, x, y, m, t, t2)) best = k;
                  }
          }
        }
        if (best < 0) {
          unc++;
          if (unc <= 200) printf("UNCOVERED N=%lld u=%lld u'=%lld\n", N, u, up);
        } else hist[best]++;
      }
  }
  for (int k = 0; k <= T; k++) printf("T=%d: %ld\n", k, hist[k]);
  printf("uncovered %ld\n", unc);
  return 0;
}

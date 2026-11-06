/* slicefind.c N mode off : for the hard thin points (mode 0: u' = u + off; mode 1: u' = 2u + off)
   outside the old regions and not covered by an edge certificate, list which slice
   (family f, orientation o, a = p c + j [t=0] or c = p a + j [t=1], direction (sg, k)) has ParOK. */
#include "../residual/slice.h"
int main(int argc, char **argv) {
  ll N = atoll(argv[1]); int mode = atoi(argv[2]); ll off = atoll(argv[3]);
  for (ll u = 2; 3 * u + 1 <= N; u++) {
    ll up = mode == 0 ? u + off : 2 * u + off;
    if (up < u || u + 2 * up > N - 1 || !isPair(N, u, up) || provenOld(N, u, up)) continue;
    if (mode == 1 && 8 * u + 320 < N) continue;
    printf("u=%lld u'=%lld (u/N=%.3f):", u, up, (double)u / N);
    int cnt = 0;
    for (int o = 0; o < 2; o++) {
      ll x = o ? up : u, y = o ? u : up;
      for (int f = 0; f < 3; f++) {
        if (f > 0 && y < 3) continue;
        ll K, R, al, be, smax, amin;
        comboParams(N, y, f, &K, &R, &al, &be, &smax, &amin);
        for (ll p = 0; p <= 3; p++)
          for (int t = 0; t < 2; t++)
            for (ll j = -3; j <= 3; j++) {
              if (t == 0) buildSlice(K, x, R, al, be, smax, amin, p, j);
              else buildSliceB(K, x, R, al, be, smax, amin, p, j);
              for (ll k = 0; k <= 4; k++)
                for (ll sg = (k == 0 ? 1 : 0); sg <= (k == 0 ? 1 : 16); sg++)
                  if (parOKdir(sg, k)) {
                    if (cnt < 6) printf(" [o%d f%d %c p%lld j%lld dir(%lld,%lld)]", o, f, t ? 'c' : 'a', p, j, sg, k);
                    cnt++;
                    goto nextj;
                  }
            nextj:;
            }
      }
    }
    printf(" total %d\n", cnt);
  }
  return 0;
}

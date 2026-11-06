/* small.c N1 N2 : the class u <= 3 (u = 2, 3): for each pair, which old region holds
   (bits: 1 B, 2 B2, 4 W, 8 D, 16 D0), printed as "N u u' N-3u' bits" for pairs not in D0. */
#include "../residual/common.h"
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]);
  for (ll N = N1; N <= N2; N++)
    for (ll u = 2; u <= 3; u++)
      for (ll v = u; u + 2 * v <= N - 1; v++) {
        if (!isPair(N, u, v)) continue;
        int b = regB(N, u, v) | regB2(N, u, v) << 1 | regW(N, u, v) << 2 | regD(N, u, v) << 3 | regD0(N, u, v) << 4;
        if (!(b & 16)) printf("%lld %lld %lld %lld %d\n", N, u, v, N - 3 * v, b);
      }
  return 0;
}

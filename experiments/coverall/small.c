/* small.c N U : the residual pairs (outside the old regions) with u <= U, any parity
   (parity ignored so that the picture is uniform), as rows u: list of u' ranges. */
#include "certs.h"
int main(int argc, char **argv) {
  ll N = atoll(argv[1]), U = atoll(argv[2]);
  for (ll u = 2; u <= U; u++) {
    printf("u=%lld:", u);
    ll start = -1, prev = -1;
    for (ll up = u; u + 2 * up <= N - 1; up++) {
      if (special(N, u, up)) continue;
      int res = !provenOld(N, u, up);
      if (res) { if (start < 0) start = up; prev = up; }
      else if (start >= 0) { printf(" [%lld,%lld]", start, prev); start = -1; }
    }
    if (start >= 0) printf(" [%lld,%lld]", start, prev);
    printf("\n");
  }
  return 0;
}

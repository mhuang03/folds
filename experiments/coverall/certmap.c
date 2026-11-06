/* certmap.c N which [G] : map over the pair triangle (any parity) of where the explicit
   certificate `which` holds ('#'), fails in the residual ('.'), fails in the old regions ('_').
   Also prints the tally of failing constraint/corner indices. */
#include "certs.h"
int main(int argc, char **argv) {
  ll N = atoll(argv[1]); int w = atoi(argv[2]);
  int G = argc > 3 ? atoi(argv[3]) : 60;
  static char mp[300][300];
  static ll fails[1000];
  for (int i = 0; i < 300; i++) for (int j = 0; j < 300; j++) mp[i][j] = ' ';
  for (ll u = 2; 3 * u + 1 <= N; u++)
    for (ll up = u; u + 2 * up <= N - 1; up++) {
      int i = u * G / N, j = up * G / N;
      Cert c = mkCert(w, N, u, up);
      int r = checkCert(N, u, up, c);
      char ch = r < 0 ? '#' : provenOld(N, u, up) ? '_' : '.';
      if (r >= 0) fails[r]++;
      if (mp[i][j] == ' ' || ch == '.' || (ch == '_' && mp[i][j] == '#')) mp[i][j] = ch;
    }
  for (int j = G / 2; j >= 0; j--) {
    printf("%5.3f ", (double)j / G);
    for (int i = 0; i <= G / 3; i++) putchar(mp[i][j]);
    printf("\n");
  }
  for (int r = 0; r < 1000; r++) if (fails[r]) printf("fail cons %d corner %d: %lld\n", r / 4, r % 4, fails[r]);
  return 0;
}

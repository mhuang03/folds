/* cover1.c N G code1 code2 ... : residual (old regions excluded, parity pairs only) covered by the
   explicit certificates; map of the LAST-needed code letter ('.' = some pair uncovered), counts,
   and with env LIST the uncovered pairs. */
#include "certs.h"
int main(int argc, char **argv) {
  ll N = atoll(argv[1]); int G = atoi(argv[2]);
  int nc = argc - 3; int codes[32];
  for (int i = 0; i < nc; i++) codes[i] = atoi(argv[3 + i]);
  static char mp[300][300]; ll cnt[33] = {0}; ll tot = 0;
  for (int i = 0; i < 300; i++) for (int j = 0; j < 300; j++) mp[i][j] = ' ';
  for (ll u = 2; 3 * u + 1 <= N; u++)
    for (ll up = u; u + 2 * up <= N - 1; up++) {
      if (!isPair(N, u, up)) continue;
      int i = u * G / N, j = up * G / N;
      if (provenOld(N, u, up)) { if (mp[i][j] == ' ') mp[i][j] = '_'; continue; }
      tot++;
      int k;
      for (k = 0; k < nc; k++) if (checkCert(N, u, up, mkCert(codes[k], N, u, up)) < 0) break;
      cnt[k]++;
      char ch = k < nc ? 'a' + k : '.';
      if (mp[i][j] == ' ' || mp[i][j] == '_' || ch == '.' || (mp[i][j] != '.' && ch > mp[i][j])) mp[i][j] = ch;
      if (k == nc && getenv("LIST"))
        printf("left u=%lld u'=%lld d=%lld e=%lld delta=%lld\n", u, up, up - u, up - 2 * u, N - 1 - u - 2 * up);
    }
  for (int j = G / 2; j >= 0; j--) {
    printf("%5.3f ", (double)j / G);
    for (int i = 0; i <= G / 3; i++) putchar(mp[i][j]);
    printf("\n");
  }
  printf("tot %lld:", tot);
  for (int k = 0; k <= nc; k++) printf(" %lld", cnt[k]);
  printf("\n");
  return 0;
}

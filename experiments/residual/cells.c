/* cells.c N : which (orientation, family, direction w1) certifies RegionPF for the pairs outside
   the old regions (exact parok.h).  Candidates are tried in a fixed order; prints the tally,
   and a map (u/N, u'/N) of the first successful candidate (digit = index, '.' = none). */
#include "parok.h"
typedef struct { int o, f; ll p, q; } Cand;
static Cand cs[] = {
  {1, 0, 1, 1}, {1, 0, 2, 1}, {1, 1, 1, 1}, {1, 1, 2, 1}, {1, 2, 1, 1}, {1, 2, 2, 1},
  {1, 0, 3, 2}, {1, 1, 3, 2}, {1, 0, 3, 1}, {0, 0, 1, 1}, {0, 1, 1, 1}, {0, 0, 1, 2}};
#define NC ((int)(sizeof cs / sizeof cs[0]))
int main(int argc, char **argv) {
  ll N = atoll(argv[1]);
  ll cnt[NC + 1] = {0};
  int G = 60;
  static char mp[100][100];
  for (int i = 0; i < 100; i++) for (int j = 0; j < 100; j++) mp[i][j] = ' ';
  for (ll u = 2; 3 * u + 1 <= N; u++)
    for (ll up = u; u + 2 * up <= N - 1; up++) {
      if (!isPair(N, u, up)) continue;
      int i = u * G / N, j = up * G / N;
      if (provenOld(N, u, up)) { if (mp[i][j] == ' ') mp[i][j] = '_'; continue; }
      int k;
      for (k = 0; k < NC; k++) {
        ll x = cs[k].o ? up : u, y = cs[k].o ? u : up;
        if (cs[k].f > 0 && y < 3) continue;
        ll K, R, al, be, smax, amin;
        comboParams(N, y, cs[k].f, &K, &R, &al, &be, &smax, &amin);
        buildCons(K, x, R, al, be, smax, amin);
        if (parOKdir(cs[k].p, cs[k].q)) break;
      }
      cnt[k]++;
      char ch = k < NC ? (k < 10 ? '0' + k : 'a' + k - 10) : '.';
      if (mp[i][j] == ' ' || mp[i][j] == '_' || ch < mp[i][j]) mp[i][j] = ch;
    }
  for (int k = 0; k < NC; k++)
    printf("%c: o=%d f=%d w1=(%lld,%lld)  %lld\n", k < 10 ? '0' + k : 'a' + k - 10, cs[k].o, cs[k].f, cs[k].p, cs[k].q, cnt[k]);
  printf(".: none %lld\n", cnt[NC]);
  for (int j = G / 2; j >= 0; j--) {
    printf("%5.3f ", (double)j / G);
    for (int i = 0; i <= G / 3; i++) putchar(mp[i][j]);
    printf("\n");
  }
  return 0;
}

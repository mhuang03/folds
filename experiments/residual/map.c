/* map.c N: residual map (columns u/N, rows u'/N), digit = 10*residual fraction */
#include <stdio.h>
#include <stdlib.h>
#include "regs.h"
int main(int argc, char **argv) {
  ll N = atoll(argv[1]);
  int G = 60;
  static int tot[100][100], res[100][100];
  for (ll u = 2; 3 * u + 1 <= N; u++)
    for (ll up = u; u + 2 * up <= N - 1; up++) {
      if ((u + N + 1 - up) % 2 != 1 || special(N, u, up)) continue;
      int i = u * G / N, j = up * G / N;
      tot[i][j]++;
      if (!(regB(N, u, up) || regB2(N, u, up) || regW(N, u, up) || regD(N, u, up) || regD0(N, u, up))) res[i][j]++;
    }
  for (int j = G / 2; j >= 0; j--) {
    printf("%5.3f ", (double)j / G);
    for (int i = 0; i <= G / 3; i++) {
      if (!tot[i][j]) printf(" ");
      else { int f = 10 * res[i][j] / tot[i][j]; printf("%c", f == 0 ? (res[i][j] ? '.' : '_') : '0' + (f > 9 ? 9 : f)); }
    }
    printf("\n");
  }
  return 0;
}

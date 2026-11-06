/* regS.c < list : reads "S N=.. u=.. u'=.." lines (output of res5) and prints the pairs not in
   Lean's RegionS (fixed shapes, u = 3 with |N - 3u'| <= 5, the corner N = 3u', u = u' - 1). */
#include <stdio.h>
typedef long long ll;
static int regionS(ll N, ll u, ll up) {
  if (N < 301) return 0;
  if (u == 2 && (up == 4 || up == 5)) return 1;
  if (u == 3 && up >= 5 && up <= 8) return 1;
  if (u == 5 && up == 5) return 1;
  if (u == 3 && (N + 1 == 3 * up || N + 3 == 3 * up || N + 5 == 3 * up || N == 3 * up + 1 ||
                 N == 3 * up + 3 || N == 3 * up + 5)) return 1;
  if (N == 3 * up && u + 1 == up) return 1;
  return 0;
}
int main(void) {
  char line[256];
  ll n = 0, left = 0;
  while (fgets(line, sizeof line, stdin)) {
    ll N, u, up;
    if (sscanf(line, "S N=%lld u=%lld u'=%lld", &N, &u, &up) != 3) continue;
    n++;
    if (regionS(N, u, up)) continue;
    left++;
    printf("%s", line);
  }
  printf("read %lld, not in RegionS %lld\n", n, left);
  return 0;
}

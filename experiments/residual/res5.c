/* res5.c < list : reads lines "L N=.. u=.. u'=.." (the output of res3 ... 1) and tests RegionSL;
   prints the pairs it does not cover ("S ...") and a count; sanity-checks dirAny for covered ones. */
#include "slice.h"
#include <string.h>
int main(void) {
  char line[256];
  ll n = 0, left = 0, bad = 0;
  while (fgets(line, sizeof line, stdin)) {
    ll N, u, up;
    if (sscanf(line, "L N=%lld u=%lld u'=%lld", &N, &u, &up) != 3) continue;
    n++;
    if (regionSL(N, u, up)) {
      if (!dirAny(N, u, up) && !dirAny(N, up, u)) { bad++; printf("BAD N=%lld u=%lld u'=%lld\n", N, u, up); }
      continue;
    }
    left++;
    printf("S N=%lld u=%lld u'=%lld d=%lld delta=%lld\n", N, u, up, up - u, N - 1 - u - 2 * up);
    fflush(stdout);
  }
  printf("read %lld left %lld bad %lld\n", n, left, bad);
  return 0;
}

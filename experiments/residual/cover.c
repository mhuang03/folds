/* cover.c N1 N2 STEP QMAX: which (orientation o, family f, direction (p, q)) PF-cover the residual.
   Prints, per candidate, the number of residual pairs it covers, and a greedy set cover. */
#include "pfcore.h"
#define MAXC 400
static int cand_o[MAXC], cand_f[MAXC], cand_p[MAXC], cand_q[MAXC], ncand;
static ll cnt[MAXC];
static unsigned char *cov; /* pairs x candidates */
int main(int argc, char **argv) {
  ll N1 = atoll(argv[1]), N2 = atoll(argv[2]), STEP = atoll(argv[3]);
  int QM = atoi(argv[4]);
  for (int o = 0; o < 2; o++)
    for (int f = 0; f < (getenv("ZONLY") ? 1 : 3); f++)
      for (int q = 0; q <= QM; q++)
        for (int p = (q == 0 ? 1 : 0); p <= (q == 0 ? 1 : 3 * q + 3); p++) {
          ll x, y;
          if (egcd(p, q, &x, &y) != 1) continue;
          cand_o[ncand] = o; cand_f[ncand] = f; cand_p[ncand] = p; cand_q[ncand] = q; ncand++;
        }
  ll cap = 4000000;
  cov = calloc(cap * ncand, 1);
  ll np = 0, nres = 0;
  for (ll N = N1; N <= N2; N += STEP)
    for (ll u = 2; 3 * u + 1 <= N; u++)
      for (ll up = u; u + 2 * up <= N - 1; up++) {
        if (!isPair(N, u, up) || provenOld(N, u, up)) continue;
        nres++;
        int any = 0;
        for (int k = 0; k < ncand; k++) {
          ll x = cand_o[k] ? up : u, y = cand_o[k] ? u : up;
          ll K, R, al, be, smax, amin;
          if (cand_f[k] > 0 && y < 2) continue;
          comboParams(N, y, cand_f[k], &K, &R, &al, &be, &smax, &amin);
          buildPi(K, x, R, al, be, smax, amin);
          if (testDir(cand_p[k], cand_q[k]) == 2) { cov[np * ncand + k] = 1; cnt[k]++; any = 1; }
        }
        if (any) np++;
        if (np >= cap) { printf("cap\n"); return 1; }
      }
  printf("residual %lld, PF-covered %lld\n", nres, np);
  for (int k = 0; k < ncand; k++) if (cnt[k]) printf("cand o=%d f=%d p=%d q=%d : %lld\n", cand_o[k], cand_f[k], cand_p[k], cand_q[k], cnt[k]);
  /* greedy */
  unsigned char *done = calloc(np, 1);
  ll left = np;
  while (left > 0) {
    ll best = -1; int bk = -1;
    for (int k = 0; k < ncand; k++) {
      ll c = 0;
      for (ll i = 0; i < np; i++) if (!done[i] && cov[i * ncand + k]) c++;
      if (c > best) { best = c; bk = k; }
    }
    if (best <= 0) break;
    for (ll i = 0; i < np; i++) if (cov[i * ncand + bk]) { if (!done[i]) left--; done[i] = 1; }
    printf("greedy: o=%d f=%d p=%d q=%d covers %lld new, left %lld\n", cand_o[bk], cand_f[bk], cand_p[bk], cand_q[bk], best, left);
  }
  return 0;
}

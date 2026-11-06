/* cert.h: exact check of an explicit ParOK certificate (Lean `ParOK (famCons ...)`):
   corners (an, cn)/Dn, (an + p1 Dn, cn + q1 Dn)/Dn, (an + p2 Dn + dn p1, cn + q2 Dn + dn q1)/Dn,
   and that one + w1; delta = dn / Dn.  Constraints: the integer forms gs[] of parok.h. */
#ifndef CERT_H
#define CERT_H
#include "../residual/parok.h"
typedef struct { LL an, cn, Dn, dn; ll p1, q1, p2, q2; int fam, o; } Cert;
/* returns -1 if all 52 conditions hold, else index 4*i + corner of the first failure */
static int worstI;
static int checkCert(ll N, ll u, ll up, Cert c) {
  ll x = c.o ? up : u, y = c.o ? u : up;
  if (c.fam > 0 && y < 3) return 999;
  if (c.Dn <= 0) return 998;
  if (c.p1 * c.q2 - c.p2 * c.q1 != 1) return 997;
  ll K, R, al, be, smax, amin;
  comboParams(N, y, c.fam, &K, &R, &al, &be, &smax, &amin);
  buildCons(K, x, R, al, be, smax, amin);
  LL ca[4], cc[4];
  ca[0] = c.an; cc[0] = c.cn;
  ca[1] = c.an + c.p1 * c.Dn; cc[1] = c.cn + c.q1 * c.Dn;
  ca[2] = c.an + c.p2 * c.Dn + c.dn * c.p1; cc[2] = c.cn + c.q2 * c.Dn + c.dn * c.q1;
  ca[3] = ca[2] + c.p1 * c.Dn; cc[3] = cc[2] + c.q1 * c.Dn;
  for (int i = 0; i < ng; i++)
    for (int k = 0; k < 4; k++)
      if (gs[i].A * ca[k] + gs[i].C * cc[k] + gs[i].D * c.Dn < 0) return 4 * i + k;
  return -1;
}
#endif

/* dc.c q1 q2: "defect chains" for the exceptional class C_1 (N = 1 mod q, q odd), PROOFS.txt
   (live3) section 3.  Work mod Q = 2q, nu2 = N mod Q in {1, q+1}.
   For a signed set P of residues mod Q (full classes of [N]) and a panel x = a (mod Q) with
   radius residue rho, Bal(P, a, rho) = sum_t P_t ([1 <= (a-t) mod Q <= rho] - [1 <= (t-a) mod Q
   <= rho]); x is balanced iff Bal = 0, for rho = (a-1) mod Q (left-half x) and
   rho = (nu2 - a) mod Q (right-half x).
   Phase X first (complete), phase Y = the other parity classes minus the class of C_1 in Y,
   placed as whole classes mod Q on background (X - its C_1 class).  Prints for each nu2 and
   each choice (X = odd / X = even) whether an order of the Y classes exists ("DC_E": X = odd,
   "DC_O": X = even). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int Q;
static int bal(const int *P, int a, int rho) {
  int s = 0;
  for (int t = 0; t < Q; t++) if (P[t]) {
    int cl = ((a - t) % Q + Q) % Q, cr = ((t - a) % Q + Q) % Q;
    s += P[t] * ((cl >= 1 && cl <= rho) - (cr >= 1 && cr <= rho));
  }
  return s;
}
int main(int argc, char **argv) {
  int q1 = atoi(argv[1]), q2 = atoi(argv[2]);
  for (int q = q1; q <= q2; q += 2) {
    Q = 2 * q;
    for (int nu2 = 1; nu2 <= q + 1; nu2 += q) {
      for (int Xpar = 1; Xpar >= 0; Xpar--) {           /* 1: X = odd residues */
        int base[64] = {0}, Y[64], ny = 0;
        int c1X = Xpar ? 1 : q + 1;                      /* residue of C_1 in X */
        int c1Y = Xpar ? q + 1 : 1;
        for (int t = 0; t < Q; t++) {
          int r = t == 0 ? Q : t;                        /* residue r in [1, Q] as t mod Q */
          if ((r & 1) == Xpar) base[t] = (r == c1X) ? 0 : 1;
          else if (r != c1Y) Y[ny++] = t;
        }
        uint8_t *ok = calloc(1u << ny, 1);
        ok[0] = 1;
        for (uint32_t S = 0; S < (1u << ny); S++) {
          if (!ok[S]) continue;
          int P[64];
          for (int t = 0; t < Q; t++) P[t] = base[t];
          for (int i = 0; i < ny; i++) if (S >> i & 1) P[Y[i]] = 1;
          for (int i = 0; i < ny; i++) {
            if (S >> i & 1) continue;
            int a = Y[i];
            int rl = ((a - 1) % Q + Q) % Q, rr = ((nu2 - a) % Q + Q) % Q;
            if (bal(P, a, rl) == 0 && bal(P, a, rr) == 0) ok[S | (1u << i)] = 1;
          }
        }
        printf("q=%d nu2=%d %s: %s\n", q, nu2, Xpar ? "DC_E (odd first)" : "DC_O (even first)",
               ok[(1u << ny) - 1] ? "yes" : "no");
        free(ok);
      }
    }
  }
}

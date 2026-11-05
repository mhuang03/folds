/* multchain.c q M: for N = 1 (mod q) and N = nu2 (mod Q), Q = M q, N >= 2Q: is there a residue
   chain mod Q (live2/PROOFS 2.2: every class balanced, at both radii, by the classes before it)
   whose LAST M classes are the classes 1, 1+q, ..., 1+(M-1)q (= the class C_1 mod q), in any
   order?  Then [N] \ C_1 (mod q) is reachable by a chain.  Prints, for each nu2 = 1 (mod q),
   yes/no.  Subset DP over the Q classes (Q <= 24). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
static int Q;
/* CycBal(A, s, rho): #{t in A: (t-s) mod Q in [1,mu]} == #{t in A: (s-t) mod Q in [1,mu]} */
static int cycbal(uint32_t A, int s, int rho) {
  int mu = rho < Q - 1 - rho ? rho : Q - 1 - rho;
  int a = 0, b = 0;
  for (int t = 1; t <= Q; t++) if (A >> (t - 1) & 1) {
    int d1 = ((t - s) % Q + Q) % Q, d2 = ((s - t) % Q + Q) % Q;
    if (d1 >= 1 && d1 <= mu) a++;
    if (d2 >= 1 && d2 <= mu) b++;
  }
  return a == b;
}
int main(int argc, char **argv) {
  int q = atoi(argv[1]), M = atoi(argv[2]);
  Q = q * M;
  uint32_t full = (1u << Q) - 1, last = 0;
  for (int i = 0; i < M; i++) last |= 1u << (i * q);       /* classes 1 + i q */
  uint8_t *reach = malloc(full + 1);
  for (int nu = 1; nu < Q; nu += q) {
    for (uint32_t S = 0; S <= full; S++) reach[S] = 0;
    reach[0] = 1;
    for (uint32_t S = 0; S <= full; S++) {
      if (!reach[S]) continue;
      int lastphase = (S & ~last) == (full & ~last);
      for (int s = 1; s <= Q; s++) {
        if (S >> (s - 1) & 1) continue;
        int inlast = (last >> (s - 1)) & 1;
        if (inlast && !lastphase) continue;
        if (!inlast && lastphase) continue;
        if (!cycbal(S, s, s - 1)) continue;
        if (!cycbal(S, s, ((nu - s) % Q + Q) % Q)) continue;
        reach[S | (1u << (s - 1))] = 1;
      }
    }
    printf("q=%d Q=%d nu2=%d: %s\n", q, Q, nu, reach[full] ? "yes" : "no");
  }
  free(reach);
}

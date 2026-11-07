"""For odd d: good class orders pi for (d, rho) (pi and mu_rho o pi valid in the d-strip),
restricted to odds-first parity blocks PB(alpha, beta).  Test whether goodness of PB(alpha,beta)
is equivalent to alpha, beta being good for some fixed parameters of the half strips."""
import sys
from rotpi2 import allvalid, valid_seq, ms
def good(p, d, rho):
    return valid_seq(p, d) and valid_seq([ms(rho + 1 - s, d) for s in p], d)
d = int(sys.argv[1]); e = d // 2
VA = allvalid(e + 1); VB = allvalid(e)
for rho in range(d):
    pairs = [(a, b) for a in VA for b in VB if good([2 * i - 1 for i in a] + [2 * i for i in b], d, rho)]
    As = set(a for a, b in pairs); Bs = set(b for a, b in pairs)
    prod = len(As) * len(Bs) == len(pairs)
    # which rho1 make "good for (e+1, rho1)" equal to As ?
    ra = [r for r in range(e + 1) if set(a for a in VA if good(a, e + 1, r)) == As]
    rb = [r for r in range(e) if set(b for b in VB if good(b, e, r)) == Bs] if e > 0 else []
    print("rho", rho, "pairs", len(pairs), "product?", prod, "|A|", len(As), "|B|", len(Bs), "A=good(e+1,r) for r in", ra, " B: r in", rb)

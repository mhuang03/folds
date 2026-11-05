"""Section 4 of PROOFS.txt: odds-first slipped tau of the 2m-strip.
First block: X1 = odds with 2e+1 replaced by 2e (e in D1), in the order alpha; second block: the
rest in the order beta (alpha, beta in V_m).  Check, for every D1 ⊆ [1, m-1] and all alpha, beta:
  validity  <=>  alpha: e+1 before p(e) = (2e+1) mod* m,  beta: q(e) = 2e mod* m before e   (e in D1)
  and, given validity, G(tau) ⊇ odds  <=>  (ii) for e in D1: p(e) not in D1 and beta: e before p(e)
                                          (i) for odd k not in 2D1+1 with e' = k mod* m in D1:
                                              alpha: (k+1)/2 before e'+1.
Usage: python3 oddslipG.py mmax"""
import sys
from eslip import gen, valid_seq

def ms(x, n): return (x - 1) % n + 1

def main():
    for m in range(2, int(sys.argv[1]) + 1):
        n = 2 * m; V = gen(m); P = [{x: i for i, x in enumerate(v)} for v in V]
        bad = tot = 0
        for bits in range(1 << (m - 1)):
            D1 = {e for e in range(1, m) if bits >> (e - 1) & 1}
            X1 = sorted([y for y in range(1, n + 1, 2) if not (y >= 3 and (y - 1) // 2 in D1)] + [2 * e for e in D1])
            rest = sorted(set(range(1, n + 1)) - set(X1))
            for ai, a in enumerate(V):
                pa = P[ai]
                okA = all(pa[e + 1] < pa[ms(2 * e + 1, m)] for e in D1)
                condI = all(pa[(k + 1) // 2] < pa[ms(k, m) + 1] for k in range(1, n, 2)
                            if not (k >= 3 and (k - 1) // 2 in D1) and ms(k, m) in D1)
                for bi, b in enumerate(V):
                    pb = P[bi]
                    okB = all(pb[ms(2 * e, m)] < pb[e] for e in D1)
                    tau = [X1[x - 1] for x in a] + [rest[x - 1] for x in b]
                    v = valid_seq(tau, n)
                    tot += 1
                    if v != (okA and okB): bad += 1; continue
                    if not v: continue
                    pt = {x: i for i, x in enumerate(tau)}
                    g = all(pt[k] < pt[ms(2 * k, n)] for k in range(1, n, 2))
                    condII = all(ms(2 * e + 1, m) not in D1 and pb[e] < pb[ms(2 * e + 1, m)] for e in D1)
                    if g != (condI and condII): bad += 1
        print(f"m={m}: {tot} checks, {bad} failures", flush=True)

if __name__ == '__main__':
    main()

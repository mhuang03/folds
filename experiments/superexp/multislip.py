"""Check that slips combine independently.
Evens-first slip set D subset [1,n-1], N = 2n:
   F_D = E - {2k : k in D} + {2k+1 : k in D}   (first block, from scratch)
   S_D = O - {2k+1 : k in D} + {2k : k in D}   (second block, after F_D)
Prediction (single slips, defect2.py): the induced system of F_D differs from the n-strip
exactly in the pairs (k, q(k)), q(k) = 2k mod* n, k in D, and S_D (with background F_D)
exactly in the pairs (k+1, p(k)), p(k) = 2k+1 mod* n, with offset -1 at k+1, k in D.
mod* n takes values in [1, n]."""
import sys, itertools, random
from defect import induced, rel

def modstar(x, n):
    return (x - 1) % n + 1

def predicted(N, D):
    n = N // 2
    pf, ps, po = set(), set(), {}
    for k in D:
        q = modstar(2 * k, n); p = modstar(2 * k + 1, n)
        # first block: index k, element q gained in R (2k<=n) or lost from L
        pf.add((k, q)); ps.add((k + 1, p)); po[k + 1] = po.get(k + 1, 0) - 1
    return pf, ps, po

def check(N, D):
    n = N // 2
    E = set(range(2, N + 1, 2)); O = set(range(1, N + 1, 2))
    F = (E - {2 * k for k in D}) | {2 * k + 1 for k in D}
    S = (O - {2 * k + 1 for k in D}) | {2 * k for k in D}
    dF, _ = induced(N, F); dS, oS = induced(N, S, F)
    pf, ps, po = predicted(N, D)
    okF = {(j, i) for (j, i, a, b) in dF} == pf
    okS = {(j, i) for (j, i, a, b) in dS} == ps and dict(oS) == po
    return okF and okS

if __name__ == '__main__':
    random.seed(1)
    for N in range(4, int(sys.argv[1]) + 1, 2):
        n = N // 2; bad = 0; tot = 0
        Ds = [c for r in range(n) for c in itertools.combinations(range(1, n), r)] if n <= 12 else \
             [tuple(k for k in range(1, n) if random.random() < 0.5) for _ in range(300)]
        for D in Ds:
            tot += 1
            if not check(N, D):
                bad += 1
                if bad <= 3: print("  mismatch N", N, "D", D)
        print(f"N={N}: {tot} slip sets, {bad} mismatches")

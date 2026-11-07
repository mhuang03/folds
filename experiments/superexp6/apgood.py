"""Search simple explicit class orders for odd d: arithmetic progressions mod d
(pi_k = a + k g mod* d) and test goodness for every rho."""
import sys
def valid_seq(seq, n):
    S = set()
    for m in seq:
        r = min(m - 1, n - m)
        if sum(1 for k in range(1, r + 1) if m - k in S) != sum(1 for k in range(1, r + 1) if m + k in S):
            return False
        S.add(m)
    return True
def ms(x, d):
    v = x % d
    return d if v == 0 else v
for d in range(3, int(sys.argv[1]) + 1, 2):
    res = {}
    for a in range(1, d + 1):
        for g in range(1, d):
            from math import gcd
            if gcd(g, d) != 1: continue
            p = [ms(a + k * g, d) for k in range(d)]
            if not valid_seq(p, d): continue
            for rho in range(d):
                if valid_seq([ms(rho + 1 - s, d) for s in p], d):
                    res.setdefault(rho, []).append((a, g))
    print(d, "valid AP orders cover rho:", sorted(res), {r: res[r][:2] for r in sorted(res)})

"""Ternary slips: N = 3n, classes c mod 3 (c = 1, 2, 3), class c = {3(y-1)+c}, placed as whole
blocks in a class order pi in V_3 (composition theorem a(3n) >= a(3) a(n)^3).
A slip exchanges two value-adjacent panels of two classes.  For a single slip, which block
triples (s1, s2, s3) in V_n^3 stay valid?  Characterise by one order condition per block.
"""
import sys
from itertools import product
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from chaincheck import V, valid_seq


def run(n, order, x, y):
    """swap panels x and y (in different classes)"""
    N = 3 * n
    Vn = V(n)
    phi = lambda c, j: 3 * (j - 1) + c
    sw = {x: y, y: x}
    good = {}
    tot = ok = 0
    res = []
    for blocks in product(Vn, repeat=3):
        seq = []
        for c, b in zip(order, blocks):
            seq += [sw.get(phi(c, j), phi(c, j)) for j in b]
        v = valid_seq(seq, N)
        tot += 1; ok += v
        res.append((blocks, v))
    # characterise: which single-block conditions 'u before w in block i' are equivalent
    chars = []
    for i in range(3):
        for u in range(1, n + 1):
            for w in range(1, n + 1):
                if u != w and all((b[i].index(u) < b[i].index(w)) == v for b, v in res):
                    chars.append((order[i], u, w))
    return ok, tot, chars


if __name__ == "__main__":
    n = int(sys.argv[1])
    N = 3 * n
    for order in [(1, 3, 2), (2, 1, 3)]:
        for x in range(1, N):
            y = x + 1
            cx, cy = (x - 1) % 3 + 1, (y - 1) % 3 + 1
            ok, tot, chars = run(n, order, x, y)
            if ok:
                print(order, f"swap {x}<->{y} (classes {cx},{cy}): {ok}/{tot}", chars if ok < tot else "ALL")

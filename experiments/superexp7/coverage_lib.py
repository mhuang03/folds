# Proven instances of hypothesis H (see coverage.py).
from functools import lru_cache
def smooth(q):
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23):
        while q % p == 0: q //= p
    return q == 1
def divisors(q):
    out = []; d = 2
    while d * d <= q:
        if q % d == 0: out.append(d)
        d += 1
    return out
@lru_cache(maxsize=None)
def H(q, r):
    if r == 0 or (q >= 2 and r in (1, q - 1)) or smooth(q): return True
    for d in divisors(q):
        for (m, j) in ((q // d, d), (d, q // d)):
            c, e = divmod(r, j)
            if H(j, e) and H(m, c) and (e == 0 or H(m, (c + 1) % m)): return True
    return False

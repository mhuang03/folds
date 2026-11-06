"""cov6.py N1 N2 [-m] [-r RULES]: the family Cov6 = Cov5 + swap + chiY.  Cov3 closed under rules:
  one   {1, N}, N odd, N != 7                                (live5 section 1)
  dbl   doubling splits N = (2j+1) n: transfer through oddRes / evenRes (both parts copies,
        each one's complement is the other copy, so both are co-reachable)
  near  nearPhi {1, 4, 6, ..., 2n} at N = 2n + 1 (complement reachable, Copies.lean)
  X     X_N = {1, 4, 6, ..., N-3, N}, N = 3 mod 4, N >= 11 (co-reachable, live5)
  cin   residue classes C_s mod q (any q) that satisfy the inward criterion themselves
  beatty  Beatty copies r -> (rN - h) // p (1 <= p, h + 2p <= N + 1) that are inward
  swap    Swap(N, p, h, c): X(N, p, h) with the last element moved to N - c (p odd, c >= 2,
          N + h >= 2cp + 1) (live6)
  chiY    N = 0 mod 4: {1, 4, 6, ..., N} = chiY([N/2]) (1 -> 1, y -> 2y) (live6)
RULES: comma separated subset (default all)."""
import os
import sys
from functools import lru_cache

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'adjacent'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'live4'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'live5'))
import covlean4 as C4  # noqa: E402
from covlean5 import inward, make_cov3  # noqa: E402

RULES = {'one', 'dbl', 'beatty', 'swap', 'chiY'}
if '-r' in sys.argv:
    i = sys.argv.index('-r')
    RULES = set(sys.argv[i + 1].split(',')) if sys.argv[i + 1] != '-' else set()
    del sys.argv[i:i + 2]


@lru_cache(maxsize=None)
def class_inward(N, q, s):
    B = set(range(s, N + 1, q))
    neg, pos = 0, N + 1
    for m in range(1, N + 1):
        if m in B:
            continue
        r = min(m - 1, N - m)
        i = sum(1 for x in range(max(1, m - r), m) if x in B) - \
            sum(1 for x in range(m + 1, m + r + 1) if x in B)
        if i < 0:
            neg = m
        elif i > 0 and m < pos:
            pos = m
    return neg < pos


def set_inward(N, B):
    neg, pos = 0, N + 1
    for m in range(1, N + 1):
        if m in B:
            continue
        r = min(m - 1, N - m)
        i = sum(1 for x in range(max(1, m - r), m) if x in B) - \
            sum(1 for x in range(m + 1, m + r + 1) if x in B)
        if i < 0:
            neg = m
        elif i > 0 and m < pos:
            pos = m
    return neg < pos


@lru_cache(maxsize=None)
def beatty_list(N):
    """[(p, image list)] for the inward Beatty copies of [N], 2 <= p < N."""
    res = []
    for p in range(2, (N + 1) // 2 + 1):
        seen = set()
        for h in (range(0, N + 2 - 2 * p) if 'beattyall' in RULES else range(0, 2)):
            X = tuple((r * N - h) // p for r in range(1, p + 1))
            if X in seen:
                continue
            seen.add(X)
            if h <= 1 or set_inward(N, set(X)):
                res.append((p, {x: i + 1 for i, x in enumerate(X)}))
    return res


@lru_cache(maxsize=None)
def swap_list(N):
    """[(p, index map)] for the swapped Beatty copies Swap(N, p, h, c)."""
    res = []
    for p in range(3, N // 4 + 1, 2):
        for h in (0, 1):
            for c in range(2, N):
                if N + h < 2 * c * p + 1:
                    break
                X = [(r * N - h) // p for r in range(1, p + 1)]
                X[-1] = N - c
                res.append((p, {x: i + 1 for i, x in enumerate(X)}))
    return res


def make_cov5(cov2):
    def cov(N, u, v):
        if u > v:
            u, v = v, u
        m = (N + 1 - v, N + 1 - u)
        return covc(N, *min((u, v), m))

    @lru_cache(maxsize=None)
    def covc(N, a, b):
        """the canonical pair (a, b) and its mirror: try every rule on both."""
        return rules(N, a, b) or rules(N, N + 1 - b, N + 1 - a)

    def rules(N, u, v):
        if C4.dead(N, u, v):
            return False
        if cov2(N, u, v) or inward(N, u, v):
            return True
        if 'one' in RULES and u == 1 and v == N and N % 2 == 1:
            return True
        # residue transfers (good classes, multiples of q when q | N+1, inward classes)
        for q in range(2, N + 1):
            if (v - u) % q:
                continue
            s = (u - 1) % q + 1
            ok = (N % q, s) in C4.good_set(q) or (s == q and (N + 1) % q == 0)
            if not ok and 'cin' in RULES:
                ok = class_inward(N, q, s)
            if not ok:
                continue
            n = (N - s) // q + 1
            if cov(n, (u - s) // q + 1, (v - s) // q + 1):
                return True
        if 'dbl' in RULES:
            for d in range(3, N + 1, 2):
                if N % d:
                    continue
                j, n = (d - 1) // 2, N // d
                ru, rv = (u - 1) % d, (v - 1) % d
                if ru % 2 == 0 and rv % 2 == 0:
                    pu = (j + 1) * ((u - 1) // d) + ru // 2 + 1
                    pv = (j + 1) * ((v - 1) // d) + rv // 2 + 1
                    if cov((j + 1) * n, pu, pv):
                        return True
                if ru % 2 == 1 and rv % 2 == 1:
                    pu = j * ((u - 1) // d) + (ru - 1) // 2 + 1
                    pv = j * ((v - 1) // d) + (rv - 1) // 2 + 1
                    if cov(j * n, pu, pv):
                        return True
        if 'near' in RULES and N % 2 == 1 and N >= 5 and u == 1 and v % 2 == 0 and v >= 4:
            if cov((N - 1) // 2, 1, v // 2):
                return True
        if 'X' in RULES and N % 4 == 3 and N >= 11:
            p = (N - 1) // 2

            def pre(x):
                if x == 1:
                    return 1
                if x == N:
                    return p
                if x % 2 == 0 and 4 <= x <= N - 3:
                    return x // 2
                return None
            pu, pv = pre(u), pre(v)
            if pu and pv and cov(p, pu, pv):
                return True
        if 'beatty' in RULES:
            for p, idx in beatty_list(N):
                if u in idx and v in idx and cov(p, idx[u], idx[v]):
                    return True
        if 'swap' in RULES:
            for p, idx in swap_list(N):
                if u in idx and v in idx and cov(p, idx[u], idx[v]):
                    return True
        if 'chiY' in RULES and N % 4 == 0 and N >= 8:
            def pre(x):
                return 1 if x == 1 else (x // 2 if x % 2 == 0 and x >= 4 else None)
            pu, pv = pre(u), pre(v)
            if pu and pv and cov(N // 2, pu, pv):
                return True
        return False
    return cov


if __name__ == '__main__':
    sys.setrecursionlimit(100000)
    args = [a for a in sys.argv[1:] if not a.startswith('-')]
    show = '-m' in sys.argv
    cov2 = C4.make_cov(True)
    cov3 = make_cov3(cov2)
    cov5 = make_cov5(cov2)  # = Cov6 with the rules above
    for N in range(int(args[0]), int(args[1]) + 1):
        P = [(u, v) for u in range(1, N + 1) for v in range(u + 1, N + 1) if not C4.dead(N, u, v)]
        c3 = sum(cov3(N, *p) for p in P)
        c5 = sum(cov5(N, *p) for p in P)
        print(N, len(P), 'Cov3', c3, 'Cov6', c5, flush=True)
        if show:
            print('   missing:', [p for p in P if not cov5(N, *p)])

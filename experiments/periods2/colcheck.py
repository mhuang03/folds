"""colcheck.py K: which orbit vertices and which chain vertices are VALID (lie in the closure of
a valid class), for K up to ~20, by the column factorisation (PROOFS2 section 2).

At an orbit vertex (x_j = T^(K-j) x_1, x_K = x_1) or a chain vertex (x_1 in {0,1},
x_{j+1} = (x_j + c_j)/2) the only tight constraints are the K - 1 consecutive halvings
(j-1, j) and the closing row (x_K = x_1, resp. the box row of x_1).  The sign of x_j relative to
x_i is fixed by v for every non-tight pair, so column j has a fixed sum s_j plus the sign of the
tight pair(s) in that column, which depends only on the side of that pair's hyperplane.
Hence the valid cells form a product over columns, and each column admits at most one side
(checked here).  Output: the valid vertices, their column sides, and (for orbit vertices) a.
"""
import sys
from fractions import Fraction as Fr
from itertools import product


def sgn_fixed(x, c):
    """sign of c relative to x (c != x, not on the arm boundaries)."""
    if x < c:
        if 2 * c < 1 + x:
            return 1
        assert 2 * c != 1 + x
        return 0
    if 2 * c > x:
        return -1
    assert 2 * c != x
    return 0


def halving_sides(cbit, s):
    """column with fixed sum s and one tight halving with bit cbit.  Returns list of
    (side, sigma) with side 'le' (u <= 0) or 'gt' (u > 0) making the column sum 0."""
    out = []
    for side in ('le', 'gt'):
        if cbit == 1:
            sig = 1 if side == 'le' else 0
        else:
            sig = 0 if side == 'le' else -1
        if s + sig == 0:
            out.append((side, sig))
    return out


def column_sums(y, tight):
    k = len(y)
    S = []
    for j in range(k):
        S.append(sum(sgn_fixed(y[i], y[j]) for i in range(j) if (i, j) not in tight))
    return S


def orbit_check(k):
    D = 2 ** (k - 1) - 1
    res = []
    for a in range(1, D):
        x1 = Fr(a, D)
        orb = [x1]
        for _ in range(k - 1):
            orb.append((2 * orb[-1]) % 1)
        if len(set(orb[:-1])) != k - 1:
            continue
        y = [orb[k - j] for j in range(1, k + 1)]
        bits = [int(2 * y[j] - y[j - 1]) for j in range(1, k)]   # c for pair (j-1, j)
        tight = {(j - 1, j) for j in range(1, k)} | {(0, k - 1)}
        S = column_sums(y, tight)
        sides = []
        ok = True
        for j in range(1, k - 1):
            opts = halving_sides(bits[j - 1], S[j])
            assert len(opts) <= 1
            if not opts:
                ok = False
                break
            sides.append(opts[0][0])
        if not ok:
            continue
        # last column: halving (k-2, k-1) and the equality with x_1
        opts = []
        for side in ('le', 'gt'):
            sig = (1 if side == 'le' else 0) if bits[k - 2] == 1 else (0 if side == 'le' else -1)
            for qside, qs in (('above', 1), ('below', -1)):
                if S[k - 1] + sig + qs == 0:
                    opts.append((side, qside))
        assert len(opts) <= 1
        if opts:
            res.append((a, y, bits, sides + [opts[0][0]], opts[0][1]))
    return res


def chain_check(k):
    res = []
    for x1 in (0, 1):
        for bits in product((0, 1), repeat=k - 1):
            if (x1 + bits[0]) % 2 == 0:
                continue
            y = [Fr(x1)]
            for c in bits:
                y.append((y[-1] + c) / 2)
            tight = {(j - 1, j) for j in range(1, k)}
            S = column_sums(y, tight)
            sides = []
            for j in range(1, k):
                opts = halving_sides(bits[j - 1], S[j])
                assert len(opts) <= 1
                if not opts:
                    break
                sides.append(opts[0][0])
            else:
                res.append((x1, y, list(bits), sides))
    return res


def first_failure(k, a):
    """(step at which the orbit vertex a/D first fails or None, word c_1..c_n)."""
    D = 2 ** (k - 1) - 1
    x1 = Fr(a, D)
    orb = [x1]
    for _ in range(k - 1):
        orb.append((2 * orb[-1]) % 1)
    y = [orb[k - j] for j in range(1, k + 1)]
    bits = [int(2 * y[j] - y[j - 1]) for j in range(1, k)]
    tight = {(j - 1, j) for j in range(1, k)} | {(0, k - 1)}
    S = column_sums(y, tight)
    for j in range(1, k - 1):
        if not halving_sides(bits[j - 1], S[j]):
            return j + 1, bits
    for side in ('le', 'gt'):
        sig = (1 if side == 'le' else 0) if bits[k - 2] == 1 else (0 if side == 'le' else -1)
        for qs in (1, -1):
            if S[k - 1] + sig + qs == 0:
                return None, bits
    return k, bits


def failstats(k):
    D = 2 ** (k - 1) - 1
    from collections import Counter
    C = Counter()
    ex = {}
    for a in range(1, D):
        x1 = Fr(a, D)
        orb = [x1]
        for _ in range(k - 1):
            orb.append((2 * orb[-1]) % 1)
        if len(set(orb[:-1])) != k - 1:
            continue
        st, bits = first_failure(k, a)
        if bits[0] != 1:
            continue
        w = ''.join(map(str, bits))
        C[st] += 1
        ex.setdefault(st, []).append(w)
    print(f'K={k}: first failing step (c_1 = 1 words):', sorted(C.items(), key=str))
    for st in sorted(ex, key=str):
        print('   ', st, ex[st][:12])


def scan(k0, k1):
    import time
    for k in range(k0, k1 + 1):
        t = time.time()
        o = orbit_check(k)
        c = chain_check(k)
        print(f'K={k}: orbit a = {[a for a, *_ in o]};  chains (x1, bits) = '
              f'{[(x1, "".join(map(str, b))) for x1, _, b, _ in c]}   ({time.time() - t:.0f}s)',
              flush=True)


if __name__ == '__main__':
    if sys.argv[1] == 'fail':
        failstats(int(sys.argv[2]))
        sys.exit()
    if sys.argv[1] == 'scan':
        scan(int(sys.argv[2]), int(sys.argv[3]))
        sys.exit()
    K = int(sys.argv[1])
    o = orbit_check(K)
    D = 2 ** (K - 1) - 1
    print(f'K={K}: D={D}; valid orbit vertices (exact period {K-1}): {len(o)}')
    for a, y, bits, sides, q in o:
        print(f'   a={a:>6} = {a}/{D}  bits(c_1..)={"".join(map(str, bits))} sides={" ".join(sides)} last {q}')
    c = chain_check(K)
    print(f'K={K}: valid chain vertices: {len(c)}')
    for x1, y, bits, sides in c:
        print(f'   x1={x1} bits={"".join(map(str, bits))}  x_K={y[-1]}  sides={" ".join(sides)}')

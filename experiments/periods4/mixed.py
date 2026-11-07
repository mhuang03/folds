"""mixed.py: the "cycle + pendant chain" vertices, which carry the mixed orders
q = 2^a d (ord_d 2 = s, d | 2^s - 1, a + s = k - 1, a >= 1, s >= 2) in c_0(T(N, k)).

Structure (PROOFS.txt section 1): a vertex v of the k-point arrangement has q | index(v) iff
  * an s-cycle: points at times t_0 < t_1 < ... < t_s with x_{t_0} = theta (exact period s,
    denominator d), x_{t_{i+1}} = the T-preimage of x_{t_i} on the orbit (T x = 2x mod 1), so
    x_{t_s} = theta again;
  * a pendant chain z_1, ..., z_a (in time order), z_1 later than its parent x_{t_j}
    (0 <= j <= s-1; j = 0 means the value theta), z_1 = the OFF-orbit preimage of x_{t_j},
    z_{i+1} = either preimage of z_i.
If z_1 hangs on theta and comes after t_s, z_1 is a halving of both copies of theta: the vertex
is non-simple (k + 1 tight rows, one dependency).

For each such vertex we determine the valid local cell (at most one, by the column rule) and
its term in the vertex formula of ../periods2/local.py at the mode e(-N/q).  Since the
character group M^{-T}Z^k/Z^k has order |det M| = q = index and <w, b> is a homomorphism onto
(1/q)Z/Z, exactly ONE character w has mode -1/q; the term is (1/q) prod_r F_r^{eps_r}(w_r).

Usage:  python3 mixed.py S A [d]      list the valid vertices and the total coefficient.
"""
import sys
import cmath
import math
from fractions import Fraction as Fr
from math import gcd

TAU = 2 * math.pi


def T(x):
    return (2 * x) % 1


def period(x):
    y, n = T(x), 1
    while y != x:
        y, n = T(y), n + 1
    return n


def thetas(s, d=None):
    """all theta with exact period s (and denominator d if given)."""
    D = 2 ** s - 1
    out = []
    for r in range(1, D):
        x = Fr(r, D)
        if period(x) != s:
            continue
        if d is not None and x.denominator != d:
            continue
        out.append(x)
    return out


def sgn(x, c):
    """sign of the later point c relative to the earlier point x (generic position)."""
    if x < c:
        if 2 * c < 1 + x:
            return 1
        assert 2 * c != 1 + x
        return 0
    if c < x:
        if 2 * c > x:
            return -1
        assert 2 * c != x
        return 0
    raise AssertionError('coincident non-tight')


# ---------------------------------------------------------------------------------------------
# tight rows of a time-ordered vertex y (tuple of Fractions in (0,1))
def tight(y):
    """list of rows (i, j, kind, c): i < j; kind 'half' (2y_j - y_i = c) or 'eq' (y_j = y_i)."""
    k = len(y)
    R = []
    for j in range(k):
        for i in range(j):
            if y[i] == y[j]:
                R.append((i, j, 'eq', 0))
            else:
                for c in (0, 1):
                    if 2 * y[j] - y[i] == c:
                        R.append((i, j, 'half', c))
    return R


def contrib(row, side):
    """contribution of a tight row to the column of its later point, on the given side
    ('le' u <= 0, 'gt' u > 0 for halvings; 'gt' / 'lt' for equalities, u = y_j - y_i)."""
    i, j, kind, c = row
    if kind == 'half':
        if c == 1:
            return 1 if side == 'le' else 0
        return -1 if side == 'gt' else 0
    return 1 if side == 'gt' else -1


def sides_of(row):
    return ('le', 'gt') if row[2] == 'half' else ('gt', 'lt')


def column_options(y, R, j):
    """valid side assignments for the tight rows in column j: list of dicts {row index: side}."""
    mine = [r for r, row in enumerate(R) if row[1] == j]
    tset = {(R[r][0], j) for r in mine}
    fixed = sum(sgn(y[i], y[j]) for i in range(j) if (i, j) not in tset)
    opts = [{}]
    for r in mine:
        opts = [{**o, r: sd} for o in opts for sd in sides_of(R[r])]
    return [o for o in opts if fixed + sum(contrib(R[r], o[r]) for r in o) == 0]


def prefix_ok(y):
    """column check of the last point of the prefix y (all earlier columns already checked)."""
    R = tight(y)
    return bool(column_options(y, R, len(y) - 1))


# ---------------------------------------------------------------------------------------------
# exact linear algebra
def solve(M, rhs):
    n = len(M)
    A = [[Fr(x) for x in M[r]] + [Fr(rhs[r])] for r in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if A[r][c] != 0)
        A[c], A[p] = A[p], A[c]
        piv = A[c][c]
        A[c] = [x / piv for x in A[c]]
        for r in range(n):
            if r != c and A[r][c] != 0:
                f = A[r][c]
                A[r] = [x - f * yv for x, yv in zip(A[r], A[c])]
    return [A[r][n] for r in range(n)]


def det(M):
    n = len(M)
    A = [[Fr(x) for x in row] for row in M]
    d = Fr(1)
    for c in range(n):
        p = next((r for r in range(c, n) if A[r][c] != 0), None)
        if p is None:
            return Fr(0)
        if p != c:
            A[c], A[p] = A[p], A[c]
            d = -d
        d *= A[c][c]
        for r in range(c + 1, n):
            f = A[r][c] / A[c][c]
            if f:
                A[r] = [x - f * yv for x, yv in zip(A[r], A[c])]
    return d


def rowvec(row, k):
    i, j, kind, c = row
    a = [0] * k
    if kind == 'half':
        a[j] += 2
        a[i] -= 1
        return a, c
    a[j] += 1
    a[i] -= 1
    return a, 0


def char_at(M, y, q):
    """the unique w in M^{-T}Z^k/Z^k with <w, b> = -1/q (mod 1); needs index(y) = q = |det M|.
    <w, b> = <n, y> for w = M^{-T} n, so pick n with <n, y> = -1/q mod 1."""
    k = len(y)
    num = [int(x * q) for x in y]          # y_i = num_i / q
    # find integers n with sum n_i num_i = -1 mod q: extended gcd
    g, coef = 0, [0] * k
    gg = q
    cq = 0                                 # coefficient of q
    # iterative extended gcd over (q, num_1, ..., num_k)
    vals = [q] + num
    cs = [[1 if t == u else 0 for t in range(k + 1)] for u in range(k + 1)]
    g, cg = vals[0], cs[0]
    for u in range(1, k + 1):
        a, b = g, vals[u]
        ca, cb = cg, cs[u]
        # ext gcd of a, b
        x0, x1, y0, y1 = 1, 0, 0, 1
        aa, bb = a, b
        while bb:
            qq = aa // bb
            aa, bb = bb, aa - qq * bb
            x0, x1 = x1, x0 - qq * x1
            y0, y1 = y1, y0 - qq * y1
        g = aa
        cg = [x0 * s1 + y0 * s2 for s1, s2 in zip(ca, cb)]
    assert g == 1, ('index != q', g)
    n = [-t for t in cg[1:]]
    MT = [list(col) for col in zip(*M)]
    w = [x % 1 for x in solve(MT, n)]
    return w


def e(x):
    return cmath.exp(1j * TAU * float(x))


def side_sum(theta, sign, closed):
    z = e(theta if sign > 0 else -theta)
    return (1 / (1 - z)) if closed else (z / (1 - z))


def F(row, side, w):
    kind = row[2]
    if kind == 'half':
        sign = -1 if side == 'le' else 1
        closed = side == 'le'
    else:
        sign = 1 if side == 'gt' else -1
        closed = False
    return side_sum(w, sign, closed)


def logmod(w):
    """log |F| = -log(2 |sin pi w|)."""
    return -math.log(2 * abs(math.sin(math.pi * float(w))))


# ---------------------------------------------------------------------------------------------
def vertex_term(y, q):
    """(term, info) for the vertex y at mode -1/q; term = None if not valid."""
    k = len(y)
    R = tight(y)
    cols = [column_options(y, R, j) for j in range(k)]
    if any(not c for c in cols):
        return None, None
    cells = [{}]
    for c in cols:
        cells = [{**a, **b} for a in cells for b in c]
    vecs = [rowvec(r, k) for r in R]
    out = 0
    used = []
    for cell in cells:
        if len(R) == k:
            basis = list(range(k))
        else:
            assert len(R) == k + 1, ('too many tight rows', y, R)
            # dependency lambda: sum lambda_r a_r = 0
            A = [vecs[r][0] for r in range(k + 1)]
            lam = nullvec(A)
            assert sum(l * vecs[r][1] for r, l in enumerate(lam)) == 0
            sig = {}
            for r, l in enumerate(lam):
                if l == 0:
                    continue
                es = -1 if cell[r] in ('le', 'lt') else 1
                sig[r] = (1 if l > 0 else -1) * es
            pos = [r for r in sig if sig[r] > 0]
            neg = [r for r in sig if sig[r] < 0]
            if not pos or not neg:
                continue                      # inconsistent (empty cone)
            assert len(pos) == 1 or len(neg) == 1
            drop = pos[0] if len(pos) == 1 else neg[0]
            basis = [r for r in range(k + 1) if r != drop]
        M = [vecs[r][0] for r in basis]
        assert abs(det(M)) == q, (y, abs(det(M)), q)
        w = char_at(M, y, q)
        assert all(x != 0 for x in w)
        t = 1 / q
        for idx, r in enumerate(basis):
            t *= F(R[r], cell[r], w[idx])
        out += t
        used.append((cell, [R[r] for r in basis], w))
    if not used:
        return None, None
    return out, used


def nullvec(A):
    """a nonzero rational vector lam with sum_r lam_r A[r] = 0 (A has k+1 rows of length k)."""
    n = len(A)
    k = len(A[0])
    # solve A^T lam = 0
    MT = [[Fr(A[r][c]) for r in range(n)] for c in range(k)]
    # gaussian elimination to RREF
    piv = []
    rr = 0
    for c in range(n):
        p = next((r for r in range(rr, k) if MT[r][c] != 0), None)
        if p is None:
            continue
        MT[rr], MT[p] = MT[p], MT[rr]
        pv = MT[rr][c]
        MT[rr] = [x / pv for x in MT[rr]]
        for r in range(k):
            if r != rr and MT[r][c] != 0:
                f = MT[r][c]
                MT[r] = [x - f * yv for x, yv in zip(MT[r], MT[rr])]
        piv.append(c)
        rr += 1
    free = [c for c in range(n) if c not in piv]
    assert len(free) == 1
    fc = free[0]
    lam = [Fr(0)] * n
    lam[fc] = Fr(1)
    for r, c in enumerate(piv):
        lam[c] = -MT[r][fc]
    return lam


# ---------------------------------------------------------------------------------------------
def structures(s, a, theta):
    """yield (orbit values list x_{t_0..t_s}, attach j, chain values z_1..z_a)."""
    orb = [theta]
    for i in range(s):
        x = orb[-1]
        pre = [x / 2, (x + 1) / 2]
        # on-orbit preimage: the one with period s
        nxt = [p for p in pre if p in orbit_set(theta)]
        assert len(nxt) == 1
        orb.append(nxt[0])
    assert orb[-1] == theta
    for j in range(s):
        P = orb[j]
        off = [p for p in (P / 2, (P + 1) / 2) if p != orb[j + 1]]
        assert len(off) == 1
        for bits in range(2 ** (a - 1)):
            z = [off[0]]
            for b in range(a - 1):
                c = (bits >> b) & 1
                z.append((z[-1] + c) / 2)
            yield orb, j, z


_orb_cache = {}


def orbit_set(theta):
    if theta not in _orb_cache:
        S = {theta}
        x = T(theta)
        while x != theta:
            S.add(x)
            x = T(x)
        _orb_cache[theta] = S
    return _orb_cache[theta]


def interleavings(orb, j, z):
    """DFS over time orders with column pruning; yields the time-ordered vertex y and the
    labels ('c', i) / ('z', i)."""
    s = len(orb) - 1
    a = len(z)
    k = s + 1 + a
    y = []
    lab = []

    def rec(ci, zi):
        if ci == s + 1 and zi == a:
            yield tuple(y), tuple(lab)
            return
        opts = []
        if ci <= s:
            opts.append(('c', ci, orb[ci]))
        if zi < a and (zi > 0 or ci > j):
            opts.append(('z', zi, z[zi]))
        for kind, idx, val in opts:
            y.append(val)
            lab.append((kind, idx))
            if prefix_ok(y):
                yield from rec(ci + (kind == 'c'), zi + (kind == 'z'))
            y.pop()
            lab.pop()

    yield from rec(0, 0)


def valid_vertices(s, a, d=-1):
    D = 2 ** s - 1
    if d == -1:
        d = D
    for theta in thetas(s, d):
        q = 2 ** a * theta.denominator
        for orb, j, z in structures(s, a, theta):
            for y, lab in interleavings(orb, j, z):
                t, info = vertex_term(y, q)
                if t is None:
                    continue
                yield dict(theta=theta, j=j, z=z, y=y, lab=lab, term=t, info=info, q=q)


def word(lab):
    return ''.join('c' if l[0] == 'c' else 'z' for l in lab)


if __name__ == '__main__':
    s = int(sys.argv[1])
    a = int(sys.argv[2])
    d = int(sys.argv[3]) if len(sys.argv) > 3 else 2 ** s - 1
    tot = 0
    n = 0
    for V in valid_vertices(s, a, d):
        n += 1
        tot += V['term']
        print(f"theta={V['theta']} j={V['j']} z={[str(x) for x in V['z']]} time={word(V['lab'])} "
              f"ns={len(V['info'][0][1]) != len(tight(V['y']))} |t|={abs(V['term']):.6g} t={V['term']:.6f}")
    print(f'(s,a)=({s},{a}) d={d} q={2**a*d}: {n} valid vertices, coefficient of e(-N/q) in c_0 = {tot}')

"""Families of valid sequences produced by the construction operations (small N).

Prints, for each N, the sizes of
  BT   : binary parity-block tree family (choice odds/evens-first at every node)
  LAD  : ladder family (choice depends only on the node's size)
  COMP : closure under parity blocks + composition (q | N)
  RES  : ... + residue chains (q not dividing N)
  ALL  : ... + slips + shifted blocks + reversal + mirror
  a(N) : all valid sequences (brute force)
and checks every member is valid.  Usage: python3 families.py [Nmax]
"""
import itertools
import sys

from brute import valid_seqs, is_valid

sys.setrecursionlimit(10000)


def scale(c, y):
    return 2 * y - c


def blocks2(sig, tau, c):
    """sig on class c (c=1 odds) first, then tau on the other class."""
    return tuple(scale(c, y) for y in sig) + tuple(scale(1 - c, y) for y in tau)


# ---------- binary tree family ----------
def bt_family(N):
    if N <= 1:
        return {tuple(range(1, N + 1))}
    out = set()
    for c in (0, 1):
        A = bt_family((N + c) // 2)
        B = bt_family((N + 1 - c) // 2)
        for s in A:
            for t in B:
                out.add(blocks2(s, t, c))
    return out


def ladder_family(N):
    """choices depend only on node size: f maps size -> bit."""
    sizes = set()
    stack = [N]
    while stack:
        n = stack.pop()
        if n >= 2 and n not in sizes:
            sizes.add(n)
            stack += [(n + 1) // 2, n // 2]
    sizes = sorted(sizes)
    out = set()
    for bits in itertools.product((0, 1), repeat=len(sizes)):
        f = dict(zip(sizes, bits))

        def g(n):
            if n <= 1:
                return tuple(range(1, n + 1))
            c = f[n]
            return blocks2(g((n + c) // 2), g((n + 1 - c) // 2), c)
        out.add(g(N))
    return out


# ---------- residue chains / composition ----------
def strip_ok(seq, q):
    return is_valid(tuple(seq), q)


def chain_orders(q, N):
    nu = N % q
    sig = lambda t: ((nu - t) % q) + 1
    res = []
    for pi in valid_seqs(q):
        if strip_ok([sig(t) for t in pi], q):
            res.append(pi)
    return res


def residue_family(N, q, C):
    out = set()
    sizes = {s: (N - s) // q + 1 for s in range(1, q + 1)}
    for pi in chain_orders(q, N):
        lists = [[tuple((y - 1) * q + s for y in o) for o in C[sizes[s]]] for s in pi]
        for combo in itertools.product(*lists):
            out.add(tuple(x for blk in combo for x in blk))
    return out


# ---------- slips ----------
def slip_family(N, C):
    if N % 2:
        return set()
    n = N // 2
    out = set()
    Vn = C[n]
    for mask in range(1 << max(n - 1, 0)):
        d = [0] * (n + 1)
        for k in range(1, n):
            if mask >> (k - 1) & 1:
                d[k] = 1
        f = [0] + [2 * i + d[i] for i in range(1, n + 1)]
        s = [0] + [2 * i - 1 - d[i - 1] for i in range(1, n + 1)]
        D = [k for k in range(1, n) if d[k]]
        ms = lambda x: ((x - 1) % n) + 1
        T = [t for t in Vn if all(t.index(k) < t.index(ms(2 * k)) for k in D)]
        S = [u for u in Vn if all(u.index(ms(2 * k + 1)) < u.index(k + 1) for k in D)]
        for t in T:
            for u in S:
                out.add(tuple(f[i] for i in t) + tuple(s[i] for i in u))
    return out


def shifted_family(N, C):
    if N % 2 or N < 4:
        return set()
    n = N // 2
    j = n // 2
    phi = lambda y: 2 * y + (y > j)
    psi = lambda y: 2 * y - 1 - (y > j + 1)
    out = set()
    for s in C[n - 1]:
        for t in C[n + 1]:
            if n % 2 == 0 and t.index(1) > t.index(j + 1):
                continue
            out.add(tuple(phi(y) for y in s) + tuple(psi(y) for y in t))
    return out


def closure(Nmax, use_res=True, use_extra=True):
    C = {0: {()}, 1: {(1,)}}
    for N in range(2, Nmax + 1):
        F = set()
        for c in (0, 1):
            for s in C[(N + c) // 2]:
                for t in C[(N + 1 - c) // 2]:
                    F.add(blocks2(s, t, c))
        for q in range(3, N):
            if N % q == 0:
                F |= residue_family(N, q, C)
            elif use_res and N >= q:
                F |= residue_family(N, q, C)
        if use_extra:
            F |= slip_family(N, C)
            F |= shifted_family(N, C)
            F |= {tuple(reversed(a)) for a in F}
            F |= {tuple(N + 1 - x for x in a) for a in F}
        C[N] = F
    return C


if __name__ == "__main__":
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 10
    Ccomp = closure(Nmax, use_res=False, use_extra=False)
    Cres = closure(Nmax, use_res=True, use_extra=False)
    Call = closure(Nmax, use_res=True, use_extra=True)
    print("N  BT  LAD  COMP  RES  ALL  a(N)   ALL/a(N)")
    for N in range(1, Nmax + 1):
        bt = bt_family(N)
        lad = ladder_family(N)
        V = set(valid_seqs(N))
        Vsym = set(valid_seqs(N, True))
        assert bt <= Vsym and lad <= bt
        assert Ccomp[N] <= V and Cres[N] <= V and Call[N] <= V, N
        assert len(bt) == 2 ** (N - 1) if N >= 1 else True
        print(N, len(bt), len(lad), len(Ccomp[N]), len(Cres[N]), len(Call[N]), len(V),
              "%.3f" % (len(Call[N]) / len(V)),
              " sym:", len(Call[N] & Vsym), len(Vsym))

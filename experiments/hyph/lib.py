"""lib.py: basic checkers for the class-order problem.

Strip validity of an order of [n]; GoodL(n, nu): pi valid and sig o pi valid with
sig(t) = ((nu - t) mod n) + 1.  xcond: the X-balance form (Lemma X of PROOFS.txt)."""
import random


def reach(n, t):
    return min(t - 1, n - t)


def step_ok(n, S, t):
    r = reach(n, t)
    return sum((t - k) in S for k in range(1, r + 1)) == sum((t + k) in S for k in range(1, r + 1))


def valid(n, seq):
    S = set()
    for t in seq:
        if not step_ok(n, S, t):
            return False
        S.add(t)
    return True


def sig(n, nu, t):
    return (nu - t) % n + 1


def goodL(n, nu, seq):
    return valid(n, seq) and valid(n, [sig(n, nu, t) for t in seq])


def md(x, n):
    """representative of x mod n in [1, n]"""
    return (x - 1) % n + 1


def xcond(n, nu, seq):
    """strip-valid and |A n X| = |A n (2s - X)| at every step, X = [1, nu]."""
    if not valid(n, seq):
        return False
    S = set()
    X = set(range(1, nu + 1))
    for s in seq:
        W = {md(2 * s - k, n) for k in range(1, nu + 1)}
        if len(S & X) != len(S & W):
            return False
        S.add(s)
    return True


def all_goodL(n, nu, extra=None, limit=None):
    """all GoodL(n, nu) orders (DFS with dead-state cache); extra(seq_prefix, t) -> bool filter."""
    res = []
    dead = set()

    def dfs(seq, S, T):
        if len(seq) == n:
            res.append(tuple(seq))
            return True
        if limit and len(res) >= limit:
            return True
        key = frozenset(S)
        if key in dead:
            return False
        ok = False
        for t in range(1, n + 1):
            if t in S:
                continue
            u = sig(n, nu, t)
            if step_ok(n, S, t) and step_ok(n, T, u) and (extra is None or extra(seq, S, t)):
                S.add(t); T.add(u); seq.append(t)
                if dfs(seq, S, T):
                    ok = True
                seq.pop(); S.discard(t); T.discard(u)
        if not ok:
            dead.add(key)
        return ok

    dfs([], set(), set())
    return res

"""brute.py: independent brute-force check of the four conventions for small N, and the
closure / containment properties.

  python3 brute.py [NMAX=7] [semi|sym]

Enumerates every ordered set partition of [N] and tests, directly from the definitions:
  (a) each m in B_i balanced w.r.t. S = B_1 u..u B_{i-1};
  (b) (a) and balanced w.r.t. S u B_i \\ {m};
  (c) every linear refinement is a valid fold sequence      [by listing the refinements];
  (d) some linear refinement is a valid fold sequence        [by listing the refinements].
Then it reports
  * W(N,k) for each convention (compare with weak.c),
  * (c) == {(a) and each block has no element in the window of another}  (the formula in weak.c),
  * containments between the conventions,
  * closure under refinement (splitting one block in two) and coarsening (merging two
    adjacent blocks), with the smallest counterexample when it fails.
"""
import sys
from itertools import permutations, product

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 7
KIND = sys.argv[2] if len(sys.argv) > 2 else 'semi'


def reach(N, m):
    return min(m - 1, N - m)


def ok_step(N, S, m):
    r = reach(N, m)
    if KIND == 'semi':
        return sum(1 for d in range(1, r + 1) if m - d in S) == sum(1 for d in range(1, r + 1) if m + d in S)
    return all(((m - d) in S) == ((m + d) in S) for d in range(1, r + 1))


def valid_seq(N, seq, S0=frozenset()):
    S = set(S0)
    for m in seq:
        if not ok_step(N, S, m):
            return False
        S.add(m)
    return True


def weak_orders(N):
    """all ordered set partitions of [1..N] as tuples of frozensets"""
    def rec(rest):
        if not rest:
            yield ()
            return
        rest = sorted(rest)
        n = len(rest)
        for mask in range(1, 1 << n):
            B = frozenset(rest[i] for i in range(n) if mask >> i & 1)
            for tail in rec(set(rest) - B):
                yield (B,) + tail
    yield from rec(set(range(1, N + 1)))


def conv_a(N, w):
    S = set()
    for B in w:
        if not all(ok_step(N, S, m) for m in B):
            return False
        S |= B
    return True


def conv_b(N, w):
    S = set()
    for B in w:
        if not all(ok_step(N, S, m) and ok_step(N, (S | B) - {m}, m) for m in B):
            return False
        S |= B
    return True


def refinements(w):
    for choice in product(*[list(permutations(sorted(B))) for B in w]):
        yield [m for blk in choice for m in blk]


def conv_c(N, w):
    return all(valid_seq(N, s) for s in refinements(w))


def conv_d(N, w):
    return any(valid_seq(N, s) for s in refinements(w))


def conv_c_formula(N, w):
    if not conv_a(N, w):
        return False
    for B in w:
        for m in B:
            for x in B:
                if x != m and abs(x - m) <= reach(N, m):
                    return False
    return True


def splits(w):
    """all weak orders obtained by splitting one block into two (ordered) parts"""
    for i, B in enumerate(w):
        el = sorted(B)
        n = len(el)
        for mask in range(1, (1 << n) - 1):
            C = frozenset(el[j] for j in range(n) if mask >> j & 1)
            yield w[:i] + (C, B - C) + w[i + 1:]


def merges(w):
    for i in range(len(w) - 1):
        yield w[:i] + (w[i] | w[i + 1],) + w[i + 2:]


def fmt(w):
    return '(' + ' | '.join(' '.join(map(str, sorted(B))) for B in w) + ')'


def main():
    convs = {'a': conv_a, 'b': conv_b, 'c': conv_c, 'd': conv_d}
    for N in range(1, NMAX + 1):
        sets = {c: set() for c in convs}
        cform = set()
        for w in weak_orders(N):
            for c, f in convs.items():
                if f(N, w):
                    sets[c].add(w)
            if conv_c_formula(N, w):
                cform.add(w)
        print('N=%d (%s)' % (N, KIND))
        for c in 'abcd':
            row = [sum(1 for w in sets[c] if len(w) == k) for k in range(1, N + 1)]
            print('   W_%s: %s' % (c, ' '.join(map(str, row))))
        print('   (c) == formula:', sets['c'] == cform)
        for x, y in (('c', 'b'), ('b', 'a'), ('c', 'd'), ('b', 'd'), ('a', 'd'), ('d', 'a')):
            bad = sorted(sets[x] - sets[y], key=lambda w: (len(w), fmt(w)))
            print('   (%s) subset of (%s): %s%s' % (x, y, not bad, '' if not bad else '   e.g. ' + fmt(bad[0])))
        for c in 'abcd':
            bad_r = [(w, v) for w in sets[c] for v in splits(w) if v not in sets[c]]
            bad_m = [(w, v) for w in sets[c] for v in merges(w) if v not in sets[c]]
            s = '   (%s) closed under refinement: %s' % (c, not bad_r)
            if bad_r:
                w, v = min(bad_r, key=lambda p: (len(p[0]), fmt(p[0])))
                s += '  e.g. %s -> %s' % (fmt(w), fmt(v))
            s += ';  under coarsening: %s' % (not bad_m)
            if bad_m:
                w, v = min(bad_m, key=lambda p: (len(p[0]), fmt(p[0])))
                s += '  e.g. %s -> %s' % (fmt(w), fmt(v))
            print(s)
        # facets: maximal elements w.r.t. refinement (c: vertices), d: facets = N-block members
        sys.stdout.flush()


if __name__ == '__main__':
    main()

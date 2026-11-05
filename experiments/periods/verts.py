"""verts.py K [shard i/n]: vertex indices (lcm of coordinate denominators) of all class polytopes
Pbar_pi for K points.  Vertices are the codimension-K faces, so by the face lemma every index
divides B(K); Theorem B (PROOFS.txt) says that for K <= 7 every index divides a single
2^a (2^s - 1) with a + s <= K - 1, and that for K = 8 the index 45 = lcm(3, 15) (two disjoint
halving cycles) is the first possible exception.  Reports the set of indices, any index not
dividing a single 2^a(2^s-1), and the classes carrying them (with the vertex)."""
import sys
from fractions import Fraction as F
from math import gcd
import PyNormaliz as PN
from poly import rows
from faces import B


def lcm(a, b):
    return a * b // gcd(a, b)


def vertices(pi):
    K = len(pi)
    ineq = [list(a) + [c] for a, c, s, t in rows(pi)]
    C = PN.Cone(inequalities=ineq, grading=[[0] * K + [1]])
    return [tuple(F(int(x), int(v[-1])) for x in v[:-1]) for v in C.ExtremeRays()]


def single(D, K):
    terms = [2 ** (K - 1)] + [2 ** (K - 1 - s) * (2 ** s - 1) for s in range(1, K)]
    return any(t % D == 0 for t in terms)


if __name__ == '__main__':
    K = int(sys.argv[1])
    si, sn = (0, 1)
    if len(sys.argv) > 2:
        si, sn = map(int, sys.argv[2].split('/'))
    types = [tuple(map(int, l.split())) for l in open(f'types_{K}.txt')][si::sn]
    seen = {}
    odd = []
    for pi in types:
        for v in vertices(pi):
            D = 1
            for x in v:
                D = lcm(D, x.denominator)
            seen[D] = seen.get(D, 0) + 1
            assert B(K) % D == 0
            if not single(D, K):
                odd.append((pi, D, v))
    print(f'K={K} shard {si}/{sn}: {len(types)} polytopes; vertex indices (with multiplicity):')
    print('  ', sorted(seen.items()))
    print(f'  indices not dividing a single 2^a(2^s-1), a+s <= {K-1}: {len(odd)}')
    for pi, D, v in odd[:40]:
        print('   ', ''.join(map(str, pi)), D, '(' + ', '.join(map(str, v)) + ')')

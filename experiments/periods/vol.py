"""vol.py K [shard i/n]: exact c_K = sum over admissible order types of vol(P_pi), P_pi the
closed continuum polytope (N = 1).  Volume = Normaliz multiplicity of the cone over P_pi
(homogeneous inequalities a.y + c t >= 0, grading t) divided by K!.  The mirror y -> 1 - y
maps the class of pi onto the class of mirror(pi) (the window rule is mirror symmetric), so
one representative per mirror pair is computed, with weight 2.
Output: volK_iofn.txt ('pi weight vol' per line, then TOTAL = partial sum of c_K)."""
import sys
from fractions import Fraction as F
from math import factorial
import PyNormaliz as PN
from poly import rows, mirror


def volume(pi):
    K = len(pi)
    ineq = [list(a) + [c] for a, c, s, t in rows(pi)]
    C = PN.Cone(inequalities=ineq, grading=[[0] * K + [1]])
    m = C.Multiplicity()
    if isinstance(m, list):
        m = F(int(m[0]), int(m[1]))
    else:
        m = F(m)
    return m / factorial(K)


if __name__ == '__main__':
    K = int(sys.argv[1])
    si, sn = (0, 1)
    if len(sys.argv) > 2:
        si, sn = map(int, sys.argv[2].split('/'))
    types = [tuple(map(int, l.split())) for l in open(f'types_{K}.txt')]
    tset = set(types)
    reps = []
    for p in types:
        q = mirror(p)
        assert q in tset
        if p < q:
            reps.append((p, 2))
        elif p == q:
            reps.append((p, 1))
    reps = reps[si::sn]
    tot = F(0)
    with open(f'vol{K}_{si}of{sn}.txt', 'w') as f:
        for n, (p, w) in enumerate(reps):
            v = volume(p)
            tot += w * v
            f.write(' '.join(map(str, p)) + f' {w} {v}\n')
            if n % 1000 == 0:
                print(n, len(reps), float(tot), file=sys.stderr, flush=True)
        f.write(f'TOTAL {tot}\n')
    print(K, si, sn, tot, float(tot), float(tot * factorial(K)))

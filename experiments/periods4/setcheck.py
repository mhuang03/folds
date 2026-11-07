"""setcheck.py K: compare, for every mixed order q = 2^a (2^s - 1) (a + s = K - 1, a >= 1, s >= 2),
the set of vertices with q | index found by Normaliz (extreme rays of all class polytopes,
../periods/types_K.txt) with the set of VALID cycle + pendant chain vertices of mixed.py.
Equality checks the classification (Prop. 1.1 + the column computation) by exhaustion."""
import sys
import os
from math import gcd

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '../periods'))
from verts import vertices                    # noqa: E402
from mixed import valid_vertices              # noqa: E402

K = int(sys.argv[1])
types = [tuple(map(int, l.split())) for l in open(os.path.join(os.path.dirname(__file__),
                                                                f'../periods/types_{K}.txt'))]
Qs = {2 ** (K - 1 - s) * (2 ** s - 1): s for s in range(2, K - 1)}
found = {q: set() for q in Qs}
for i, pi in enumerate(types):
    for v in vertices(pi):
        D = 1
        for x in v:
            D = D * x.denominator // gcd(D, x.denominator)
        for q in Qs:
            if D % q == 0:
                found[q].add(v)
    if i % 5000 == 0:
        print(f'  {i}/{len(types)}', flush=True)
ok = True
for q, s in sorted(Qs.items(), key=lambda t: t[1]):
    a = K - 1 - s
    mine = {V['y'] for V in valid_vertices(s, a)}
    same = mine == found[q]
    ok &= same
    print(f'K={K} q={q} (s={s}, a={a}): Normaliz {len(found[q])} vertices, structures {len(mine)}: '
          f'{"EQUAL" if same else "DIFFERENT"}', flush=True)
    if not same:
        print('   only Normaliz:', list(found[q] - mine)[:5])
        print('   only mixed.py:', list(mine - found[q])[:5])
print('ALL EQUAL' if ok else 'MISMATCH')

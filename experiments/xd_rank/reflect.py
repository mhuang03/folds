"""Reflection positivity test (Freedman-Lovasz-Schrijver style) for the cut matrices.

For a cut that the mirror m -> N+1-m maps to its complement (spatial middle cut of even N;
parity cut of even N), put
     K[sigma, sigma'] = M[sigma, mirror(sigma')]           (mirror applied entrywise).
Mirror invariance gives K = K^T.  Composing with reversal gives a second symmetric form
     K'[sigma, sigma'] = M[sigma, reverse(mirror(sigma'))].
A "reflection positive" gluing (as for graph homomorphism numbers) would make K positive
semidefinite.  We print the inertia (numbers of positive / negative / zero eigenvalues).
usage: python3 reflect.py N kind [params]
"""
import os
import subprocess
import sys
import numpy as np
from descriptor import cut_set


def main():
    N = int(sys.argv[1])
    kind = sys.argv[2]
    params = sys.argv[3:]
    X = cut_set(N, kind, params)
    Y = [y for y in range(1, N + 1) if y not in set(X)]
    assert sorted(N + 1 - x for x in X) == Y, 'mirror must exchange X and Y'
    here = os.path.dirname(os.path.abspath(__file__))
    fn = os.path.join(here, 'out', 'dump_refl_%d_%s.txt' % (N, kind))
    subprocess.run([os.path.join(here, 'cutmat.bin'), str(N), kind] + params + ['dump', fn],
                   check=True, stdout=subprocess.DEVNULL)
    rows = []
    sig = []
    cols = None
    for line in open(fn):
        if line.startswith('# cols:'):
            cols = [tuple(int(v) for v in c.split(',')) for c in line.split()[2:]]
            continue
        s, r = line.split(' :')
        sig.append(tuple(int(v) for v in s.split(',')))
        rows.append([int(v) for v in r.split()])
    os.remove(fn)
    M = np.array(rows, dtype=float)
    ci = {c: i for i, c in enumerate(cols)}
    for name, f in (('mirror', lambda s: tuple(N + 1 - v for v in s)),
                    ('reverse-mirror', lambda s: tuple(N + 1 - v for v in reversed(s)))):
        # the nonzero columns are exactly the images of the nonzero rows
        perm = [ci[f(s)] for s in sig]
        K = M[:, perm]
        assert np.array_equal(K, K.T), 'K not symmetric'
        ev = np.linalg.eigvalsh(K)
        tol = 1e-7 * max(abs(ev))
        pos = int((ev > tol).sum())
        neg = int((ev < -tol).sum())
        print('N=%d %s %s  size=%d  inertia (+,-,0) = (%d, %d, %d)   lambda_max=%.4g  lambda_min=%.4g  '
              'trace=%d' % (N, kind, name, len(sig), pos, neg, len(ev) - pos - neg, ev[-1], ev[0],
                            int(round(np.trace(K)))))


if __name__ == '__main__':
    main()

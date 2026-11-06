"""fsearch2.py: test parametric families F for 'F and complement inward' (see fsearch.py)."""
import sys
from zeroset import inward_set


def fams(n):
    yield 'ev-4', {n - 1} | set(range(2, n - 3, 2))
    yield 'ev-2', {n - 1} | set(range(2, n - 1, 2))
    yield 'mod3', {2, n - 1} | {x for x in range(2, n - 1) if x % 3 == 2}
    yield 'mod3b', {2, n - 1} | {x for x in range(2, n - 2) if x % 3 == 2}
    yield 'mod3m', {2, n - 1} | {x for x in range(3, n) if x % 3 == (n - 1) % 3}
    for q in range(4, 8):
        for s in range(q):
            yield f'mod{q},{s}', {2, n - 1} | {x for x in range(3, n - 1) if x % q == s}
    for a in range(3, n - 1):
        for b in range(a, n - 1):
            yield f'int[{a},{b}]', {2, n - 1} | set(range(a, b + 1))


for n in range(int(sys.argv[1]), int(sys.argv[2]) + 1, 2):
    good = []
    for name, F in fams(n):
        Fc = set(range(1, n + 1)) - F
        if inward_set(n, F) and inward_set(n, Fc):
            good.append(name)
    print(n, good[:12], flush=True)

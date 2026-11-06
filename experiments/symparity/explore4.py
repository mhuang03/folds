"""u = first panel of the parity class C not containing a_1, z = a_N, p = #panels before u.
Test: does (u+v)/2 precede u for every v in C with v = z (mod 4)?  Also report the
minimum of p - |{v in C : v = z mod 4}|."""
import sys
from apfree import enum

Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
for N in range(3, Nmax + 1):
    L = enum(N)
    bad = 0
    slack = None
    for w in L:
        pos = {x: t for t, x in enumerate(w)}
        i = next(t for t in range(N) if w[t] % 2 != w[0] % 2)
        u, z = w[i], w[-1]
        Cz = [v for v in range(1, N + 1) if v % 4 == z % 4]
        if any(pos[(u + v) // 2] > i for v in Cz):
            bad += 1
        s = i - len(Cz)
        slack = s if slack is None else min(slack, s)
    print(f'N={N:2d} sequences violating: {bad}   min p-|C_z| = {slack}')

"""D = class of a_1, C = the other class.  Test candidate structural statements:
 S1: x in C, y in D, 2y - x in [1,N]  =>  y before x
 S2: x in C, y in D, 2x - y in [1,N]  =>  y before x
 S0: y in D, u = first of C, 2y - u in [1,N]  =>  y before u"""
import sys
from apfree import enum

Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 11
for N in range(3, Nmax + 1):
    L = enum(N)
    bad = [0, 0, 0]
    for w in L:
        pos = {x: t for t, x in enumerate(w)}
        D = [x for x in range(1, N + 1) if x % 2 == w[0] % 2]
        C = [x for x in range(1, N + 1) if x % 2 != w[0] % 2]
        u = min(C, key=lambda x: pos[x])
        b1 = any(1 <= 2 * y - x <= N and pos[y] > pos[x] for x in C for y in D)
        b2 = any(1 <= 2 * x - y <= N and pos[y] > pos[x] for x in C for y in D)
        b0 = any(1 <= 2 * y - u <= N and pos[y] > pos[u] for y in D)
        bad[0] += b1; bad[1] += b2; bad[2] += b0
    print(f'N={N:2d} s={len(L)} violations S1 {bad[0]}  S2 {bad[1]}  S0 {bad[2]}')

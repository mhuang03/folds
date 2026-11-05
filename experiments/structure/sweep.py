"""Compute many derived sequences and look them up in OEIS."""
import sys
import numpy as np
from common import *
from oeis import lookup

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 15
seqs = {}

def add(name, vals):
    seqs[name] = vals

def mirror(S, N):
    return int(bin(S)[2:].zfill(N)[::-1], 2)

# variants
for mode, par in [("mod2", 0), ("ge", 0), ("left", 0), ("cap", 1), ("cap", 2), ("cap", 3)]:
    add(f"{mode}{par or ''}", [int(g_array(N, mode, par)[(1 << N) - 1]) for N in range(1, NMAX + 1)])

first1, firstmid, rm, h, T3, Tm2, live_mid, nreach, nlive, dead = [], [], [], [], [], [], [], [], [], []
for N in range(1, NMAX + 1):
    g = g_array(N); full = (1 << N) - 1; pc = popcounts(N); f = f_array(g, N)
    first1.append(int(f[1]))
    if N % 2: firstmid.append(int(f[1 << (N // 2)]))
    # reversal-mirror fixed sequences: sum over S with M(S)=complement (minus middle) of g(S)
    c = 0
    k = N // 2
    for S in np.nonzero((g > 0) & (pc == k))[0]:
        S = int(S); M = mirror(S, N)
        rest = full ^ S ^ M
        if S & M: continue
        if N % 2 == 0 and rest == 0: c += int(g[S])
        if N % 2 == 1 and rest == 1 << (N // 2) and step_ok(S, N // 2 + 1, N): c += int(g[S])
    rm.append(c)
    T3.append(int(g[pc == 3].sum()) if N >= 3 else 0)
    Tm2.append(int(g[pc == N - 2].sum()) if N >= 2 else 0)
    nreach.append(int((g > 0).sum()))
    nlive.append(int(((g > 0) & (f > 0)).sum()))
    dead.append(int(((g > 0) & (f == 0)).sum()))
for n in range(1, (NMAX + 1) // 2 + 1):
    N = 2 * n - 1
    h.append(int(g_array(N)[(1 << n) - 1]))
add("first=1", first1); add("first=mid(odd N)", firstmid); add("RM-fixed", rm)
add("h(n)=g([1..n]) in long strip", h); add("T(N,3)", T3); add("T(N,N-2)", Tm2)
add("#reachable S", nreach); add("#live S", nlive); add("#dead reachable S", dead)
add("RM-fixed/?", rm)
for name, v in seqs.items():
    print(name, v)
    vv = v[:]
    while vv and vv[0] in (0, 1): vv = vv[1:]
    res = lookup(vv[:12]) if len(vv) >= 4 else []
    for r in res[:3]: print("   ", *r)
    if not res: print("    (no OEIS match)")

"""beatty_chain.py N1 N2: for each Beatty window copy X = X(N,p,g) (2p-1-N <= g <= 0), look for a
Beatty copy Z = X(N,P,G) with X ⊊ Z such that the preimage of X in the P-world is again a
Beatty copy X(P,p,g') (2p-1-P <= g' <= 0).  Then X's completability reduces to that of Z (in
the N-world) and of the preimage (in the P-world).  Report, per N, the copies that have no
such Z, i.e. the 'top' copies."""
import sys


def beatty(N, p, g):
    return tuple((r * N + g) // p for r in range(1, p + 1))


def copies(N):
    out = {}
    for p in range(1, N + 1):
        for g in range(2 * p - 1 - N, 1):
            X = beatty(N, p, g)
            out.setdefault(X, (p, g))
    return out


CACHE = {}


def copyset(n):
    if n not in CACHE:
        CACHE[n] = copies(n)
    return CACHE[n]


for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    C = copyset(N)
    tops = []
    for X, (p, g) in C.items():
        if p == N:
            continue
        found = False
        for Z, (P, G) in C.items():
            if P <= p or P == N or not set(X) <= set(Z):
                continue
            pre = tuple(i + 1 for i, z in enumerate(Z) if z in set(X))
            if pre in copyset(P):
                found = True
                break
        if not found:
            tops.append((p, g, X))
    print(N, "tops:", sorted(tops))

"""Shared helpers: enumeration of valid (semi-symmetric) sequences, windows, signs."""
import sys

def reach(N, m):
    return min(m - 1, N - m)

def masks(N):
    L = [0] * (N + 1); R = [0] * (N + 1)
    for m in range(1, N + 1):
        for d in range(1, reach(N, m) + 1):
            L[m] |= 1 << (m - d - 1); R[m] |= 1 << (m + d - 1)
    return L, R

def valid_step(N, S, m, L, R):
    return bin(S & L[m]).count("1") == bin(S & R[m]).count("1")

def valid_seqs(N, constrained=None):
    """Generate all valid sequences (tuples).  constrained: set of panels with a constraint."""
    L, R = masks(N)
    if constrained is not None:
        for m in range(1, N + 1):
            if m not in constrained:
                L[m] = R[m] = 0
    pc = lambda x: bin(x).count("1")
    seq = []
    def rec(S):
        if len(seq) == N:
            yield tuple(seq); return
        for m in range(1, N + 1):
            b = 1 << (m - 1)
            if S & b: continue
            if pc(S & L[m]) != pc(S & R[m]): continue
            seq.append(m)
            yield from rec(S | b)
            seq.pop()
    yield from rec(0)

def is_valid(N, a, L=None, R=None):
    if L is None: L, R = masks(N)
    S = 0
    for m in a:
        if bin(S & L[m]).count("1") != bin(S & R[m]).count("1"): return False
        S |= 1 << (m - 1)
    return True

def sign(a):
    n = len(a); inv = 0
    for i in range(n):
        for j in range(i + 1, n):
            if a[i] > a[j]: inv += 1
    return -1 if inv & 1 else 1

def near(N, x, y):
    """x, y do not commute: one lies in the window of the other."""
    return abs(x - y) <= max(reach(N, x), reach(N, y))

A = [None, 1, 2, 4, 10, 28, 96, 256, 1120, 4256, 17878, 70960, 383476, 1620328, 9167908,
     47821296, 276182312, 1481994716, 10084180418, 55082188120, 398874108930, 2505681033958,
     18168130281086, 119006527671252, 979730153850974, 6564449510287388, 55581983250573500,
     413109755332919448, 3603074636066234798, 27545080998591561856, 262878496654501774250,
     2037247307316034896720, 20222490725552617395966, 171668579369815966705184,
     1711977358970374039688092, 14916356465581456801127844, 162918548122441960881265188,
     1435459602925600924848243286, 15884954204816776206921874682]

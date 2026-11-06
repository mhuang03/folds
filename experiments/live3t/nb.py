# nb.py: helpers for closed-form near maps (regularity, images, Theorem G after steps)
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'live3s'))
from base import reach, L, R, valid, valid3, dead3, inward1, centre

def rel(n, j, y):
    r = reach(n, j)
    if j - r <= y < j: return 1
    if j < y <= j + r: return -1
    return 0

def irregular(N, p, phi):
    """panels j of [p] at which phi is not regular"""
    return [j for j in range(1, p + 1)
            if any(rel(N, phi(j), phi(y)) != rel(p, j, y) for y in range(1, p + 1))]

def increasing(N, p, phi):
    v = [phi(y) for y in range(1, p + 1)]
    return all(1 <= x <= N for x in v) and all(v[i] < v[i + 1] for i in range(p - 1))

def steps_ok(N, S, ms, c=None):
    """valid steps ms after S, then Theorem G (any centre, or centre 1/2 if c == 1)"""
    S = set(S)
    for m in ms:
        if not valid(N, S, m): return False
        S.add(m)
    return inward1(N, S) if c == 1 else centre(N, S)

def deadpair(n, u, v):
    return u == 1 and v == n and ((n % 2 == 0 and n >= 4) or n == 7)

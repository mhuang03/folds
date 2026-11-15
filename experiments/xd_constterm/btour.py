#!/usr/bin/env python3
"""Balanced-tournament relaxation B(N) and variants, exact (Python ints).

A tournament on [N] = for every pair x<y a choice of which is "earlier".
D_m = #{x in L(m): x earlier than m} - #{y in R(m): y earlier than m}.
B = number of tournaments with D_m = 0 for all constrained m.

Variants (arms):
  true     L(m) = [m-r, m-1], R(m) = [m+1, m+r], r = min(m-1, N-m)
  full     L(m) = [1, m-1],   R(m) = [m+1, N]            (all windows complete)
  left     true arms, but only m <= (N+1)/2 constrained   (nested prefix windows)
  radR     r = min(m-1, N-m, R)

DP: add vertices y = 1..N, orient pairs (x,y), x<y, one at a time; state = partial D of the
active vertices; a vertex is checked (D = 0) and dropped when its last right-arm element has
been added.  brute(): direct 2^C(N,2) enumeration for cross-checking.
"""
import sys, itertools

def arms(N, variant):
    L = {}; R = {}
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        if variant == 'full':
            L[m] = set(range(1, m)); R[m] = set(range(m + 1, N + 1))
            continue
        if variant.startswith('rad'):
            r = min(r, int(variant[3:]))
        L[m] = set(range(m - r, m)); R[m] = set(range(m + 1, m + r + 1))
        if variant == 'left' and 2 * m > N + 1:
            L[m] = set(); R[m] = set()
    return L, R

def B(N, variant='true'):
    L, R = arms(N, variant)
    last = {m: (max(R[m]) if R[m] else m) for m in range(1, N + 1)}
    states = {(): 1}          # tuple of D for active vertices (sorted by vertex)
    active = []
    for y in range(1, N + 1):
        states = {s + (0,): c for s, c in states.items()}
        active.append(y)
        iy = len(active) - 1
        for ix, x in enumerate(active[:-1]):
            A = x in L[y]; Bf = y in R[x]
            if not A and not Bf:
                continue
            new = {}
            for s, c in states.items():
                # orientation x first
                if A:
                    t = s[:iy] + (s[iy] + 1,)
                else:
                    t = s
                new[t] = new.get(t, 0) + c
                # orientation y first
                if Bf:
                    if s[ix] == 0: continue
                    t = s[:ix] + (s[ix] - 1,) + s[ix + 1:]
                else:
                    t = s
                new[t] = new.get(t, 0) + c
            states = new
        # pairs (x,y) with x no longer active or with neither relation
        act = set(active)
        mult = 0
        for x in range(1, y):
            A = x in L[y]; Bf = y in R[x]
            if x in act:
                if not A and not Bf: mult += 1
            else:
                assert not Bf
                if A:
                    # x dropped but in L(y): orientation changes D_y only
                    new = {}
                    for s, c in states.items():
                        new[s] = new.get(s, 0) + c
                        t = s[:iy] + (s[iy] + 1,)
                        new[t] = new.get(t, 0) + c
                    states = new
                else:
                    mult += 1
        if mult:
            states = {s: c << mult for s, c in states.items()}
        keep = [i for i, x in enumerate(active) if last[x] > y]
        drop = [i for i, x in enumerate(active) if last[x] <= y]
        if drop:
            new = {}
            for s, c in states.items():
                if any(s[i] != 0 for i in drop): continue
                t = tuple(s[i] for i in keep)
                new[t] = new.get(t, 0) + c
            states = new
            active = [active[i] for i in keep]
        rem = [sum(1 for z in R[x] if z > y) for x in active]
        states = {s: c for s, c in states.items() if all(s[i] <= rem[i] for i in range(len(s)))}
    assert not active
    return states.get((), 0)

def brute(N, variant='true'):
    L, R = arms(N, variant)
    pairs = [(x, y) for x in range(1, N + 1) for y in range(x + 1, N + 1)]
    cnt = 0
    for bits in itertools.product((0, 1), repeat=len(pairs)):
        D = [0] * (N + 1)
        for (x, y), b in zip(pairs, bits):
            if b == 0:   # x earlier
                if x in L[y]: D[y] += 1
            else:
                if y in R[x]: D[x] -= 1
        if not any(D): cnt += 1
    return cnt

if __name__ == '__main__':
    variant = sys.argv[1] if len(sys.argv) > 1 else 'true'
    Nmax = int(sys.argv[2]) if len(sys.argv) > 2 else 12
    for N in range(1, Nmax + 1):
        b = B(N, variant)
        extra = ''
        if N <= 6:
            bb = brute(N, variant); assert bb == b, (N, b, bb)
            extra = ' (brute ok)'
        print(N, b, extra, flush=True)

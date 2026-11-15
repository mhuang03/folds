#!/usr/bin/env python3
"""(1) AO(N) = number of ALL traces of the fixed independence relation I_N with every panel
    once (= acyclic orientations of the dependence graph = classes of S_N under swaps of
    independent adjacent entries).  Cartier-Foata:  AO(N) = sum_k (-1)^k r_k(I_N) (N-k)!,
    r_k = number of k-matchings of I_N (rook numbers of a Ferrers board).  Compared with the
    subset DP (kdp mode t) and factored.
(2) quick recurrence tests on K(N) (number of valid traces), N = 1..28:
    P-recursive  sum_{i<=r} p_i(N) K(N+i) = 0, deg p_i <= d   (exact, mod a large prime).
"""
import re, sys
from math import factorial

def indep(N, x, y):
    if x > y: x, y = y, x
    return 2 * x <= y and x + N + 1 <= 2 * y

def matchings(N):
    # rows: left panels x; columns: right panels y. Count k-matchings by DP over rows with
    # the Ferrers property (row sets are nested), checked explicitly.
    rows = []
    for x in range(1, N + 1):
        cols = frozenset(y for y in range(x + 1, N + 1) if indep(N, x, y))
        if cols: rows.append(cols)
    rows.sort(key=len)
    nested = all(rows[i] <= rows[i + 1] for i in range(len(rows) - 1))
    r = [1]
    for i, c in enumerate(rows):          # nested: a new rook has len(c) - (#rooks so far) choices
        new = [0] * (len(r) + 1)
        for k, v in enumerate(r):
            new[k] += v
            if len(c) - k > 0: new[k + 1] += v * (len(c) - k)
        r = new
    return r, nested, [len(c) for c in rows]

def factor(n):
    f = {}; p = 2
    while p * p <= n:
        while n % p == 0: f[p] = f.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return ' '.join(f"{p}^{e}" for p, e in sorted(f.items()))

dp = {}; K = {}
for line in open('dp_out.txt'):
    m = re.match(r'N=(\d+) mode=(.) value=(-?\d+)', line)
    if m and m.group(2) == 't': dp[int(m.group(1))] = int(m.group(3))
    if m and m.group(2) == 'k': K[int(m.group(1))] = int(m.group(3))
print("N  AO(N) [Cartier-Foata rook formula]  check-vs-DP  Ferrers  row lengths  factorisation")
for N in range(1, 31):
    r, nested, rl = matchings(N)
    ao = sum((-1) ** k * rk * factorial(N - k) for k, rk in enumerate(r))
    chk = 'n/a' if N not in dp or N >= 23 else ('ok' if dp[N] == ao else 'MISMATCH')
    A_, B_ = N // 2, N - N // 2            # chordal (perfect elimination) product formula
    prod = factorial(B_)
    for i, b in enumerate(sorted(rl + [0] * (A_ - len(rl))), start=1): prod *= B_ - b + i
    print(N, ao, chk, nested, rl, 'product_formula_ok' if prod == ao else 'PRODUCT MISMATCH',
          '|', factor(ao))

# ---- recurrence test on K
P = (1 << 61) - 1
def rank_mod(rows):
    rows = [r[:] for r in rows]; rk = 0; ncol = len(rows[0])
    for c in range(ncol):
        piv = next((i for i in range(rk, len(rows)) if rows[i][c] % P), None)
        if piv is None: continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][c], P - 2, P)
        rows[rk] = [v * inv % P for v in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][c] % P:
                f = rows[i][c]
                rows[i] = [(a - f * b) % P for a, b in zip(rows[i], rows[rk])]
        rk += 1
    return rk
Ks = [K[n] for n in range(1, 29)]
print("\nP-recursive test on K(1..28): (order r, degree d) unknowns equations rank -> fit?")
for r in range(1, 8):
    for d in range(0, 6):
        unk = (r + 1) * (d + 1); eqs = 28 - r
        if eqs < unk + 3: continue
        rows = [[(n ** j) * Ks[n - 1 + i] % P for i in range(r + 1) for j in range(d + 1)]
                for n in range(1, eqs + 1)]
        rk = rank_mod(rows)
        print(f"  r={r} d={d} unknowns={unk} eqs={eqs} rank={rk} {'FIT' if rk < unk else 'no'}")
print("\nratios K(N)/K(N-1):", ' '.join(f"{Ks[i]/Ks[i-1]:.3f}" for i in range(1, 28)))
A = {}
for line in open('../semi_counts.txt'):
    f = line.split()
    if f and f[0].isdigit(): A[int(f[0])] = int(f[1])
print("mean class size a(N)/K(N):", ' '.join(f"{A[n]/K[n]:.1f}" for n in range(1, 29)))

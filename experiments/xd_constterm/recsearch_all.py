#!/usr/bin/env python3
"""P-recursive / ODE recurrence search (engine of experiments/recsearch) on the sequences
of this directory: a_d(N) (d = 2..5), B(N), B(N)/Bprod(N) numerators, E(j) = c(2j),
signed counts, left-half permutation counts, radius-R tournament counts (normalised).
Also a plain C-finite (constant-coefficient) test via Berlekamp-Massey over Q.
"""
import sys, os, io
from fractions import Fraction
from math import comb
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'recsearch'))
import precursive
from btour import arms

def col(fn, c=1, pref=None):
    out = []
    for l in open(os.path.join(HERE, fn)):
        f = l.split()
        if pref is not None:
            if f[0] != pref: continue
            f = f[1:]
        out.append(int(f[c]))
    return out

def bm(s):
    """Berlekamp-Massey over Q: returns the minimal recurrence length."""
    s = [Fraction(x) for x in s]
    C = [Fraction(1)]; Bp = [Fraction(1)]; L = 0; m = 1; b = Fraction(1)
    for n in range(len(s)):
        d = s[n] + sum(C[i] * s[n - i] for i in range(1, L + 1))
        if d == 0:
            m += 1
        elif 2 * L <= n:
            T = C[:]
            C = C + [Fraction(0)] * (len(Bp) + m - len(C))
            for i, x in enumerate(Bp): C[i + m] -= d / b * x
            L = n + 1 - L; Bp = T; b = d; m = 1
        else:
            C = C + [Fraction(0)] * (len(Bp) + m - len(C))
            for i, x in enumerate(Bp): C[i + m] -= d / b * x
            m += 1
    return L, C[:L + 1]

def normalised(variant):
    """B_variant(N) / Bprod(N) as exact fractions."""
    B = col(f'B_{variant}.txt')
    out = []
    for N in range(1, len(B) + 1):
        L, R = arms(N, variant)
        prod = Fraction(2 ** comb(N, 2))
        for m in range(1, N + 1):
            r = len(R[m]); prod *= Fraction(comb(2 * r, r), 4 ** r)
        out.append(Fraction(B[N - 1]) / prod)
    return out

seqs = {}
ap = [list(map(int, l.split())) for l in open(os.path.join(HERE, 'ap_table.txt'))]
for j, d in enumerate([0, 2, 3, 4, 5]):
    seqs[f'a_{d}' if d else 'a (check)'] = [row[1 + j] for row in ap]
seqs['B'] = col('B_true.txt')
seqs['E(j)=c(2j)'] = col('prefix_even.txt', 1, 'E')
sg = col('signed_counts.txt')
seqs['signed, N odd'] = sg[0::2]
seqs['signed, N=2 mod 4'] = sg[1::4]
lp = col('left_perm_counts.txt')
seqs['left-half perms (odd N)'] = lp[0::2]
seqs['B_left (odd N)'] = col('B_left.txt')[0::2]

print("== C-finite test (Berlekamp-Massey over Q; a genuine recurrence has order << len/2)")
for v in ('rad2', 'rad3', 'rad4', 'true', 'left'):
    nz = normalised(v)
    if v == 'left': nz = nz[0::2]
    L, C = bm(nz[3:])
    print(f"  B_{v}/Bprod from N=4: {len(nz) - 3} terms, minimal linear recurrence order {L}",
          ('-> C-finite: ' + ' '.join(str(-c) for c in C[1:])) if 2 * L + 2 <= len(nz) - 3 else '(no recurrence)')
for name, s in seqs.items():
    L, C = bm(s)
    print(f"  {name}: {len(s)} terms, minimal linear recurrence order {L}", '(no recurrence)' if 2 * L + 2 > len(s) else 'RECURRENCE')

print("== P-recursive / ODE search (all shapes with >= 5 spare equations)")
detail = io.StringIO()
for name, s in seqs.items():
    try:
        summ, found = precursive.run(name, [None] + list(s), detail)
    except TypeError:
        print(f"  {name}: too few terms for any ansatz with 5 spare equations")
        continue
    print(' ', summ, flush=True)
    for f in found:
        print('     RELATION', f[0], f[1], f[2], f[3]['kernel'][:1])

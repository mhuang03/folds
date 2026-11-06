"""Family 1: P-recursive (holonomic) relations for a(N), c(N) and transforms.

Two ansatz shapes, both linear in the unknowns:
  REC(r,d):  sum_{i=0..r} sum_{j=0..d} c_ij n^j s(n-i) = 0            for n = n0..L
             (equivalently a theta-ODE of order d with polynomial degree r for the OGF)
  ODE(r,d):  sum_{i=0..r} sum_{j=0..d} c_ij x^j D^i F(x) = 0, F = sum s(n) x^n,
             compared at x^n for n = d+1..L-r (s(0) never used); this is a
             recurrence of order r+d and degree r with only (r+1)(d+1) unknowns.
All (r,d) with E >= K+5 (K = (r+1)(d+1) unknowns, E equations) are tried.  REC is
also run with the first 6 equations dropped (a recurrence that only holds for large n).
Output: per sequence, every (shape, r, d) tried, and a summary line.
"""
import sys
from fractions import Fraction
from math import factorial
from common import A, C, NMAX, analyze, fmt
import transforms as T

SPARE = 5


def rec_rows(s, r, d, skip=0):
    L = len(s) - 1
    rows = []
    for n in range(r + 1 + skip, L + 1):
        rows.append([Fraction(n) ** j * s[n - i] for i in range(r + 1) for j in range(d + 1)])
    return rows


def ode_rows(s, r, d):
    L = len(s) - 1
    rows = []
    for n in range(d + 1, L - r + 1):
        row = []
        for i in range(r + 1):
            for j in range(d + 1):
                m = n - j + i          # coefficient of x^n in x^j D^i F is (m)_i s(m), m=n-j+i
                ff = 1
                for t in range(i):
                    ff *= (m - t)
                row.append(ff * s[m])
        rows.append(row)
    return rows


def sequences():
    a = A
    seqs = {
        'a': a,
        'a/N!': T.over_fact(a),
        'binom(a), a0=0': T.binomial(a, 0),
        'binom(a), a0=1': T.binomial(a, 1),
        'invbinom(a), a0=1': T.inv_binomial(a, 1),
        'OGF log(1+A)': T.ogf_log(a),
        'OGF exp(A)': T.ogf_exp(a),
        'OGF 1/(1+A)': T.ogf_inv(a),
        'EGF log(1+A)': T.egf_log(a),
        'EGF exp(A)': T.egf_exp(a),
        'EGF 1/(1+A)': T.egf_inv(a),
        'c (N<=41)': C,
        'c(2n)': [None] + [C[2 * n] for n in range(1, (len(C) - 1) // 2 + 1)],
        'c(4n+1)': [None] + [C[4 * n + 1] for n in range(0, (len(C) - 2) // 4 + 1)],
        'c(4n)': [None] + [C[4 * n] for n in range(1, (len(C) - 1) // 4 + 1)],
        'c(4n+2)': [None] + [C[4 * n + 2] for n in range(0, (len(C) - 3) // 4 + 1)],
        '(a+c)/4 orbits': [None] + [Fraction(a[n] + C[n], 4) for n in range(1, NMAX + 1)],
        '(a-c)/4': [None] + [Fraction(a[n] - C[n], 4) for n in range(1, NMAX + 1)],
        'a(2n)': [None] + [a[2 * n] for n in range(1, NMAX // 2 + 1)],
        'a(2n+1)': [None] + [a[2 * n + 1] for n in range(0, (NMAX - 1) // 2 + 1)],
    }
    return seqs


def run(name, s, out):
    L = len(s) - 1
    best = None
    found = []
    tried = 0
    maxK = 0
    for shape in ('REC', 'REC-skip6', 'ODE'):
        for r in range(0, L):
            for d in range(0, L):
                K = (r + 1) * (d + 1)
                if r == 0:
                    continue         # r = 0 is p(n) s(n) = 0: only spurious solutions
                if shape == 'ODE':
                    E = L - r - d
                elif shape == 'REC':
                    E = L - r
                else:
                    E = L - r - 6
                if E < K + SPARE or K < 2:
                    continue
                if shape == 'REC':
                    rows = rec_rows(s, r, d)
                    tcols = list(range(d + 1))
                elif shape == 'REC-skip6':
                    rows = rec_rows(s, r, d, 6)
                    tcols = list(range(d + 1))
                else:
                    rows = ode_rows(s, r, d)
                    tcols = None
                res = analyze(rows, tcols)
                tried += 1
                maxK = max(maxK, K)
                line = f"  {name:22s} {shape:9s} r={r:2d} d={d:2d}  " + fmt(res)
                print(line, file=out)
                if res['kernel']:
                    found.append((shape, r, d, res))
                if best is None or res['excess'] > best[0]:
                    best = (res['excess'], shape, r, d)
    summ = (f"{name:22s} L={L:2d}  ansatze={tried:3d}  max K={maxK:2d}  "
            f"relations={len(found)}  max excess={best[0]:+d} at {best[1]} r={best[2]} d={best[3]}")
    return summ, found


if __name__ == '__main__':
    out = open('precursive_detail.txt', 'w')
    print(__doc__, file=out)
    summaries = []
    for name, s in sequences().items():
        summ, found = run(name, s, out)
        print(summ, flush=True)
        summaries.append(summ)
        for f in found:
            print('   RELATION', f[0], f[1], f[2], fmt(f[3]), f[3]['kernel'][:1], flush=True)
    print('\nSUMMARY', file=out)
    for s in summaries:
        print(s, file=out)

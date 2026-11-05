"""The parity-slip recursion  a(2n) >= 2^{|C_n|} * a(ceil(n/2))^2 * a(floor(n/2))^2.

Inputs: tau, sigma = ODDS-FIRST parity-block sequences of [n]
   (2x - 1 for x in alpha) ++ (2y for y in beta),  alpha in V_{ceil(n/2)}, beta in V_{floor(n/2)},
and any D subset C_n,  C_n = {k odd in [1, n-1]} (n even), {k odd : 2k + 1 <= n} (n odd).
For k in C_n: k is odd and q(k) = 2k mod* n is even, so tau places k before q(k);
p(k) = (2k+1) mod* n is odd and k + 1 even, so sigma places p(k) before k + 1.
This script builds ALL these sequences for small n, checks validity by brute force and
distinctness, and compares the count with the formula."""
import itertools, sys
from family import valid, compose_slip

def all_valid(n):
    out = []
    def rec(seq, placed):
        if len(seq) == n:
            out.append(tuple(seq)); return
        for m in range(1, n + 1):
            if m in placed:
                continue
            r = min(m - 1, n - m)
            if sum((m - d) in placed for d in range(1, r + 1)) == sum((m + d) in placed for d in range(1, r + 1)):
                placed.add(m); seq.append(m); rec(seq, placed); seq.pop(); placed.remove(m)
    rec([], set())
    return out

def Cn(n):
    return [k for k in range(1, n) if k % 2 and (n % 2 == 0 or 2 * k + 1 <= n)]

V = {k: all_valid(k) for k in range(0, 8)}
for n in range(1, int(sys.argv[1]) + 1):
    hi, lo = (n + 1) // 2, n // 2
    par = [tuple(2 * x - 1 for x in al) + tuple(2 * y for y in be) for al in V[hi] for be in V[lo]]
    C = Cn(n)
    seqs = []
    for r in range(len(C) + 1):
        for D in itertools.combinations(C, r):
            for t in par:
                for s in par:
                    seqs.append(compose_slip(n, s, None, t, None, D)[0])
    ok = all(valid(sq, 2 * n) for sq in seqs)
    pred = 2 ** len(C) * (len(V[hi]) * len(V[lo])) ** 2
    print(f"N = 2n = {2*n}: |C_n| = {len(C)}, sequences = {len(seqs)} (formula {pred}), "
          f"distinct = {len(set(seqs))}, all valid = {ok}")

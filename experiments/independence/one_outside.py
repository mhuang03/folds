"""Brute-force check of the one-outside-element case (PROOFS.txt section 4) for even N.

N = 2n+2, b = n+2 (window [2, N]), a with W_a ⊆ {1} ∪ L_b (i.e. 2a <= n+2);
mirror: b = n+1, W_a ⊆ R_b ∪ {N}.  Checks
   #(C_a and C_b) * (2r_a+1)! * (2r_b+1)! == N! * 4^r_a r_a!^2 * 4^r_b r_b!^2,
and the chain corollary (Lean: card_constrSeqs_chain_one_outside) for chains [m, a, b]
where W_m is compatible with a and with b.
Usage: python3 one_outside.py 6 8 10
"""
import itertools
import math
import sys


def reach(N, m):
    return min(m - 1, N - m)


def window(N, m):
    r = reach(N, m)
    return set(range(m - r, m + r + 1))


def arms(N, m):
    r = reach(N, m)
    return set(range(m - r, m)), set(range(m + 1, m + r + 1))


def compat(N, A, b):
    L, R = arms(N, b)
    return b not in A and (A <= L or not (A & L)) and (A <= R or not (A & R))


def w(r):
    return 4 ** r * math.factorial(r) ** 2, math.factorial(2 * r + 1)


def check(N):
    n = (N - 2) // 2
    pairs = []
    for a in range(1, N + 1):
        if window(N, a) <= {1} | arms(N, n + 2)[0]:
            pairs.append((a, n + 2))
        if window(N, a) <= {N} | arms(N, n + 1)[1]:
            pairs.append((a, n + 1))
    chains = []
    for a, b in pairs:
        chains.append((a, b))
        for m in range(1, N + 1):
            if m in (a, b):
                continue
            if compat(N, window(N, m), a) and compat(N, window(N, m), b):
                chains.append((m, a, b))
    panels = sorted({x for c in chains for x in c})
    cnt = {c: 0 for c in chains}
    for perm in itertools.permutations(range(1, N + 1)):
        pos = [0] * (N + 1)
        for i, x in enumerate(perm):
            pos[x] = i
        ok = {}
        for m in panels:
            r = reach(N, m)
            p = pos[m]
            lc = sum(1 for d in range(1, r + 1) if pos[m - d] < p)
            rc = sum(1 for d in range(1, r + 1) if pos[m + d] < p)
            ok[m] = lc == rc
        for c in chains:
            if all(ok[m] for m in c):
                cnt[c] += 1
    bad = 0
    for c in chains:
        lhs, rhs = cnt[c], math.factorial(N)
        for m in c:
            num, den = w(reach(N, m))
            lhs *= den
            rhs *= num
        if lhs != rhs:
            bad += 1
        print(f"N={N} chain {c}: count={cnt[c]} {'ok' if lhs == rhs else 'FAIL'}")
    print(f"N={N}: {len(chains)} chains, failures={bad}")
    sys.stdout.flush()


if __name__ == "__main__":
    for N in map(int, sys.argv[1:] or ["6", "8"]):
        check(N)

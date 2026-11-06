"""Odd-N slip lemma (PROOFS.txt, Theorem O), exhaustive check.

N = 2n+1, D ⊆ [1, n], d = indicator of D.
  slip(D, tau, sigma) = tau.map(i -> 2i + d_i) ++ sigma.map(i -> 2i - 1 - d_{i-1}),
  tau in V_n (first block: the evens, 2k -> 2k+1 for k in D),
  sigma in V_{n+1} (second block: the odds, 2k+1 -> 2k for k in D).
Claimed sufficient conditions (for every k in D):
  (F)  tau   places k before qq_n(k) = 2k mod* n
  (S)  sigma places pp_{n+1}(k) = (2k+1) mod* (n+1) before k+1
  (W)  k = n+1 (mod 2), k <= n-1:  tau   places (k+n+1)/2 before k
       k = n   (mod 2):            sigma places k+1 before (k+n+2)/2
(conditions "x before x" are vacuous).  Also computes the EXACT criterion from the
general slip lemma (Theorem A of superexp3) and checks it is necessary and sufficient.

Checks per block: the first block's validity depends only on tau, the second block's
only on sigma (on top of the complete first block), so "conds => valid" and "exact <=> valid"
are checked for every D, every tau in V_n and every sigma in V_{n+1}: this covers every
triple (D, tau, sigma).  For N <= 11 also all pairs (tau, sigma) whole-sequence.
usage: python3 oddslip.py [Nmax]
"""
import sys
from itertools import combinations


def valid_step(S, m, N):
    r = min(m - 1, N - m)
    return sum(1 for d in range(1, r + 1) if m - d in S) == \
        sum(1 for d in range(1, r + 1) if m + d in S)


def valid_seq(seq, N, start=()):
    S = set(start)
    for m in seq:
        if not valid_step(S, m, N):
            return False
        S.add(m)
    return True


def V(n):
    out = []

    def rec(pre, S):
        if len(pre) == n:
            out.append(tuple(pre))
            return
        for m in range(1, n + 1):
            if m not in S and valid_step(S, m, n):
                S.add(m)
                pre.append(m)
                rec(pre, S)
                pre.pop()
                S.discard(m)
    rec([], set())
    return out


def ms(x, n): return (x - 1) % n + 1


def before(t, x, y):
    """x is placed before y (vacuous if x == y)."""
    return x == y or t.index(x) < t.index(y)


def tau_conds(D, n, t):
    for k in D:
        if not before(t, k, ms(2 * k, n)):
            return False
        if (k - n - 1) % 2 == 0 and k <= n - 1 and not before(t, (k + n + 1) // 2, k):
            return False
    return True


def sigma_conds(D, n, s):
    for k in D:
        if not before(s, ms(2 * k + 1, n + 1), k + 1):
            return False
        if (k - n) % 2 == 0 and not before(s, k + 1, (k + n + 2) // 2):
            return False
    return True


def below(T, y): return sum(1 for x in T if x <= y)


def cyc(m, T, z): return below(T, z % m) + (z // m) * len(T)


def exact_first(d, n, t):
    """Theorem A for the first block, evaluated: E_j = 2j-1+d_j-w_j."""
    N = 2 * n + 1
    for k, j in enumerate(t):
        T = t[:k]
        w = d(2 * j - n - 1 + d(j)) if 4 * j - 1 + 2 * d(j) >= N else 0
        if cyc(n, T, 2 * j - 1 + d(j) - w) != 2 * below(T, j - 1):
            return False
    return True


def exact_second(d, n, s):
    N = 2 * n + 1
    for k, j in enumerate(s):
        U = s[:k]
        e = d(j - 1)
        w = d(2 * j - 2 - e - n) if 4 * j - 3 - 2 * e >= N else 0
        if (2 * j - 2 - e - w) + cyc(n + 1, U, 2 * j - 1 - e + w) != 2 * (j - 1 - e) + 2 * below(U, j - 1):
            return False
    return True


def subsets(xs):
    for r in range(len(xs) + 1):
        yield from combinations(xs, r)


def main():
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 17
    for N in range(3, Nmax + 1, 2):
        n = N // 2
        Vt, Vs = V(n), V(n + 1)
        nd = bad_suff = valid_cnt = cond_cnt = bad_exact = 0
        for D in subsets(range(1, n + 1)):
            Ds = set(D)
            f = [0] + [2 * i + (1 if i in Ds else 0) for i in range(1, n + 1)]
            g = [0] + [2 * i - 1 - (1 if (i - 1) in Ds else 0) for i in range(1, n + 2)]
            first = set(f[1:])

            def dd(i, Ds=Ds): return 1 if i in Ds else 0
            assert len(first) == n and first | set(g[1:]) == set(range(1, N + 1))
            for t in Vt:
                v = valid_seq([f[i] for i in t], N)
                c = tau_conds(D, n, t)
                if exact_first(dd, n, t) != v:
                    bad_exact += 1
                nd += 1
                valid_cnt += v
                cond_cnt += c
                if c and not v:
                    bad_suff += 1
            for s in Vs:
                v = valid_seq([g[i] for i in s], N, first)
                c = sigma_conds(D, n, s)
                if exact_second(dd, n, s) != v:
                    bad_exact += 1
                nd += 1
                valid_cnt += v
                cond_cnt += c
                if c and not v:
                    bad_suff += 1
        print(f"N={N}: a(n)={len(Vt)} a(n+1)={len(Vs)} block checks={nd} "
              f"valid={valid_cnt} conds={cond_cnt} conds-but-invalid={bad_suff} exact-mismatch={bad_exact}", flush=True)
        if N <= 11:
            # whole sequences, all pairs, all D: conds => valid, and validity splits by blocks
            bad = tot = 0
            for D in subsets(range(1, n + 1)):
                Ds = set(D)
                f = [0] + [2 * i + (1 if i in Ds else 0) for i in range(1, n + 1)]
                g = [0] + [2 * i - 1 - (1 if (i - 1) in Ds else 0) for i in range(1, n + 2)]
                for t in Vt:
                    ct = tau_conds(D, n, t)
                    for s in Vs:
                        seq = [f[i] for i in t] + [g[i] for i in s]
                        tot += 1
                        if ct and sigma_conds(D, n, s) and not valid_seq(seq, N):
                            bad += 1
            print(f"   whole sequences: {tot} triples, conds-but-invalid={bad}", flush=True)


if __name__ == "__main__":
    main()

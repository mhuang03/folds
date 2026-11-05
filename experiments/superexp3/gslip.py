"""General slip lemma.  N = 2n, X any n-subset of [2n], f = sorted X, s = sorted complement,
kappa(y) = |X ∩ [1,y]|, lambda(y) = y - kappa(y), extended cyclically:
kappa~(2n a + y) = n a + kappa(y).  For tau, sigma in V_n the sequence (f_tau, s_sigma) is valid iff
   for every j:  no x in I_j is placed before j in tau,     I_j = cyc(2j - 1, kappa~(2 f_j - 1))
                 every x in J_j is placed before j in sigma, J_j = cyc(2j - 1, lambda~(2 s_j - 1))
where cyc(a, b) is the multiset of indices (y mod* n) for y in (min(a,b), max(a,b)].
(For I_j: the condition says #placed in I_j = 0;  for J_j: #placed in J_j = |J_j| as a multiset.)
Exhaustive check: all X, all tau, sigma in V_n, n <= nmax.  Usage: python3 gslip.py nmax"""
import sys, itertools
from eslip import gen, valid_seq

def ms(x, n):
    return (x - 1) % n + 1

def intervals(X, n):
    N = 2 * n
    Xs = set(X)
    kap = [0] * (N + 1)
    for y in range(1, N + 1):
        kap[y] = kap[y - 1] + (y in Xs)
    def kt(y):  # kappa~
        a, r = divmod(y, N)
        return n * a + kap[r]
    def lt(y):
        return y - kt(y)
    f = sorted(Xs); s = [y for y in range(1, N + 1) if y not in Xs]
    I, J = {}, {}
    for j in range(1, n + 1):
        for (seq, fn, D) in ((f, kt, I), (s, lt, J)):
            a, b = 2 * j - 1, fn(2 * seq[j - 1] - 1)
            lo, hi = min(a, b), max(a, b)
            D[j] = [ms(y, n) for y in range(lo + 1, hi + 1)]
    return f, s, I, J

def check(t, sg, I, J, n):
    pt = {m: i for i, m in enumerate(t)}; ps = {m: i for i, m in enumerate(sg)}
    for j in range(1, n + 1):
        if any(pt[x] < pt[j] for x in I[j]): return False
        # every element of J_j (with multiplicity) placed before j
        if any(not (ps[x] < ps[j]) for x in J[j]): return False
        if len(J[j]) != len(set(J[j])): return False
    return True

def main():
    nmax = int(sys.argv[1])
    for n in range(1, nmax + 1):
        V = gen(n); bad = 0; tot = 0; nval = 0
        for X in itertools.combinations(range(1, 2 * n + 1), n):
            f, s, I, J = intervals(X, n)
            for t in V:
                for sg in V:
                    v = valid_seq([f[x - 1] for x in t] + [s[x - 1] for x in sg], 2 * n)
                    c = check(t, sg, I, J, n)
                    tot += 1; nval += v
                    if v != c: bad += 1
        print(f"n={n}: checks={tot} valid={nval} mismatches={bad}", flush=True)

if __name__ == '__main__':
    main()

"""The slip family F(N): an explicit super-exponential family of semi-symmetric fold sequences.

Members are pairs (seq, S) where seq is a valid sequence of [N] whose FIRST block is
"evens-like" and S is its SECOND block ("odds-like"):
  * N = 2n (slip node): for sigma', tau' in F(n), put sigma = rev sigma', tau = rev tau'
    (these start with their odds-like block).  For D subset G(sigma, tau)
        f_i = 2i + d_i,  s_i = 2i - 1 - d_{i-1}      (d_i = [i in D])
        seq = (f_{tau_1}, ..., f_{tau_n}, s_{sigma_1}, ..., s_{sigma_n}),  S = {s_i}.
    G(sigma, tau) = { k in [1, n-1] : k in first(tau), q(k) in second(tau),
                                      p(k) in first(sigma), k+1 in second(sigma) }
    with q(k) = 2k mod* n, p(k) = 2k+1 mod* n (values in [1, n]); first(rev rho) is the
    second block of rho.  These four memberships force the order conditions of the slip
    lemma (tau: k before q(k); sigma: p(k) before k+1).
  * N = 2m+1 (parity node): seq = (2 * x for x in rho1) + (2y - 1 for y in rho2) with
    rho1 in F(m), rho2 in F(m+1) (any members), S = odds.
  * N = 1: ((1,), {1}).

F*(N) uses every D subset G; F_s(N) uses |D| = s(N) only (the counted family of the proof).
"""
import random, sys, itertools
from functools import lru_cache

def modstar(x, n):
    return (x - 1) % n + 1

def valid(seq, N):
    """Brute-force check that seq (a permutation of 1..N) is semi-symmetric (Fenwick tree)."""
    tree = [0] * (N + 1)
    def add(i):
        while i <= N:
            tree[i] += 1; i += i & -i
    def pref(i):
        s = 0
        while i > 0:
            s += tree[i]; i -= i & -i
        return s
    if sorted(seq) != list(range(1, N + 1)):
        return False
    for m in seq:
        r = min(m - 1, N - m)
        left = pref(m - 1) - pref(m - 1 - r)
        right = pref(m + r) - pref(m)
        if left != right:
            return False
        add(m)
    return True

def good_set(n, sig_first, tau_first):
    """sig_first / tau_first: sets of elements of the FIRST block of sigma / tau (in [1,n])."""
    G = []
    for k in range(1, n):
        q = modstar(2 * k, n); p = modstar(2 * k + 1, n)
        if k in tau_first and q not in tau_first and p in sig_first and (k + 1) not in sig_first:
            G.append(k)
    return G

def compose_slip(n, sig, sig_first, tau, tau_first, D):
    d = [0] * (n + 2)
    for k in D:
        d[k] = 1
    f = [0] + [2 * i + d[i] for i in range(1, n + 1)]
    s = [0] + [2 * i - 1 - d[i - 1] for i in range(1, n + 1)]
    seq = tuple(f[t] for t in tau) + tuple(s[t] for t in sig)
    return seq, frozenset(s[1:])

def members_all(N):
    """F*(N), exhaustively (small N)."""
    if N == 1:
        return [((1,), frozenset({1}))]
    if N % 2 == 1:
        m = N // 2
        return [(tuple(2 * x for x in r1) + tuple(2 * y - 1 for y in r2), frozenset(range(1, N + 1, 2)))
                for r1, _ in members_all(m) for r2, _ in members_all(m + 1)]
    n = N // 2
    out = []
    M = members_all(n)
    for sp, Sp in M:           # sigma = rev sp, first(sigma) = Sp
        for tp, Tp in M:
            G = good_set(n, Sp, Tp)
            for r in range(len(G) + 1):
                for D in itertools.combinations(G, r):
                    out.append(compose_slip(n, sp[::-1], Sp, tp[::-1], Tp, D))
    return out

def sample(N, s_of, rng):
    """A random member of F_s(N) (|D| = s_of(N) at every slip node).  Raises if G is too small."""
    if N == 1:
        return (1,), frozenset({1})
    if N % 2 == 1:
        m = N // 2
        r1, _ = sample(m, s_of, rng); r2, _ = sample(m + 1, s_of, rng)
        return tuple(2 * x for x in r1) + tuple(2 * y - 1 for y in r2), frozenset(range(1, N + 1, 2))
    n = N // 2
    sp, Sp = sample(n, s_of, rng); tp, Tp = sample(n, s_of, rng)
    G = good_set(n, Sp, Tp)
    s = s_of(N)
    if len(G) < s:
        raise RuntimeError(f"G too small at N={N}: {len(G)} < {s}")
    D = rng.sample(G, s)
    return compose_slip(n, sp[::-1], Sp, tp[::-1], Tp, D)

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'all':
        for N in range(1, int(sys.argv[2]) + 1):
            M = members_all(N)
            seqs = [m[0] for m in M]
            ok = all(valid(sq, N) for sq in seqs)
            print(f"N={N}: |F*(N)| = {len(seqs)}, distinct = {len(set(seqs))}, all valid = {ok}")
    else:
        K = float(sys.argv[2]); Nmax = int(sys.argv[3]); trials = int(sys.argv[4])
        s_of = lambda N: int((N // 2) / K)
        rng = random.Random(7)
        for N in list(range(2, 200)) + [256, 300, 511, 512, 513, 1000, 1024, 2048, 3000, 4096]:
            if N > Nmax:
                break
            bad = 0
            for _ in range(trials):
                sq, _ = sample(N, s_of, rng)
                if not valid(sq, N):
                    bad += 1
            if bad or N in (256, 512, 1024, 2048, 4096):
                print(f"N={N}: {trials} random members, {bad} invalid")
        print("done")

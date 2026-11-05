"""cgood.py K: palindromic chains with the transversal X_r (PROOFS.txt section 2).

q = 2k + 1, nu = 4r + 1 < q, t0 = 2r + 1, phi(i) = 2i (i <= r), 2i + 1 (i > r) (X_r = evens
below t0, odds above), psi(i) = 2i - 1 (i <= r), 2i (i > r) (sig X_r), sigma = sig_{k, 2r}.
pi = phi(beta), t0, reverse(psi(sigma(beta))) is a chain iff phi(beta) and psi(sigma(beta))
are valid from scratch in the q-strip.

Prints per (k, r) the starts phi(b) obtained (ground truth, subset DP in the q-strip), and
checks the reformulation: phi(beta) valid  <=>  beta valid in the k-strip + Prec1, and
psi(sigma beta) valid  <=>  sigma beta valid in the k-strip + Prec2 (pairwise window
agreement except at the listed pairs), for every step and every placed set.
"""
import sys


def reach(N, m):
    return min(m - 1, N - m)


def bal_list(N, S, m):
    r = reach(N, m)
    return sum(1 for x in S if m - r <= x < m) == sum(1 for x in S if m < x <= m + r)


def exc1(k, r, i, j):   # j placed before i breaks agreement of phi
    return (j == 2 * i and r < i and 2 * i <= k) or (j == 2 * i - k and 1 <= j <= r)


def exc2(k, r, i, j):   # for psi
    return j == 2 * i - 1 and i <= r and 2 * i - 1 > r


def agree_check(K):
    """window agreement of phi/psi with the k-strip except at exc pairs"""
    for k in range(1, K + 1):
        q = 2 * k + 1
        for r in range(0, k):
            if 4 * r + 1 >= q:
                break
            phi = lambda i: 2 * i if i <= r else 2 * i + 1
            psi = lambda i: 2 * i - 1 if i <= r else 2 * i
            for f, ex in ((phi, exc1), (psi, exc2)):
                for i in range(1, k + 1):
                    for j in range(1, k + 1):
                        if j == i:
                            continue
                        x, y = f(i), f(j)
                        rq, rk = reach(q, x), reach(k, i)
                        a = (x - rq <= y < x, x < y <= x + rq)
                        b = (i - rk <= j < i, i < j <= i + rk)
                        if (a != b) != ex(k, r, i, j):
                            print('MISMATCH', k, r, f.__name__ if hasattr(f, '__name__') else f, i, j, a, b)
                            return False
    return True


def starts(k, r):
    q = 2 * k + 1
    phi = lambda i: 2 * i if i <= r else 2 * i + 1
    psi = lambda i: 2 * i - 1 if i <= r else 2 * i
    sg = lambda i: (2 * r - i) % k + 1
    full = (1 << k) - 1
    memo = {}

    def fin(S):
        if S == full:
            return True
        if S in memo:
            return memo[S]
        placed = [i for i in range(1, k + 1) if S >> (i - 1) & 1]
        P1 = [phi(i) for i in placed]
        P2 = [psi(sg(i)) for i in placed]
        res = False
        for i in range(1, k + 1):
            if S >> (i - 1) & 1:
                continue
            if bal_list(q, P1, phi(i)) and bal_list(q, P2, psi(sg(i))) and fin(S | 1 << (i - 1)):
                res = True
                break
        memo[S] = res
        return res

    return [phi(b) for b in range(1, k + 1) if fin(1 << (b - 1))]


if __name__ == '__main__':
    K = int(sys.argv[1])
    print('agreement except at Prec pairs:', agree_check(K))
    for k in range(1, K + 1):
        for r in range(1, k):
            if 4 * r + 1 >= 2 * k + 1:
                break
            print('q', 2 * k + 1, 'nu', 4 * r + 1, 'k', k, 'r', r, 'starts', starts(k, r))

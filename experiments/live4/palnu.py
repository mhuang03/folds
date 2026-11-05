"""palnu.py q1 q2: palindromic rotation-stable sequences for every nu (odd q).

pi is palindromic for nu if sig o pi = reverse(pi), sig(t) = (nu - t) mod q + 1.  Then pi is a
chain iff pi is valid; for odd q, pi = (x_1..x_k, t0, sig x_k, .., sig x_1) with t0 the fixed
point of sig, and pi is valid iff x and sig o x are valid from scratch and t0 is balanced by
the set of x.  Prints, per (q, nu), the starts t = x_1 (and sig t) reachable this way, compared
with the non-exceptional classes (Conjecture RS).  Subset DP, 1 core, small memory.
"""
import sys


def win(q):
    L, R = [0] * (q + 1), [0] * (q + 1)
    for m in range(1, q + 1):
        r = min(m - 1, q - m)
        for d in range(1, r + 1):
            L[m] |= 1 << (m - d)
            R[m] |= 1 << (m + d)
    return L, R


def bal(S, m, L, R):
    return bin(S & L[m]).count('1') == bin(S & R[m]).count('1')


def starts(q, nu):
    L, R = win(q)
    sg = [0] + [(nu - t) % q + 1 for t in range(1, q + 1)]
    t0 = [t for t in range(1, q + 1) if sg[t] == t][0]
    k = (q - 1) // 2
    # completable[S]: from state S (x-set; sig-set implied) we can finish
    memo = {}

    def sgset(S):
        T = 0
        for t in range(1, q + 1):
            if S >> t & 1:
                T |= 1 << sg[t]
        return T

    def fin(S, cnt):
        if S in memo:
            return memo[S]
        if cnt == k:
            r = bal(S, t0, L, R)
            memo[S] = r
            return r
        T = sgset(S)
        r = False
        for t in range(1, q + 1):
            if t == t0 or (S >> t & 1) or (T >> t & 1):
                continue
            if bal(S, t, L, R) and bal(T, sg[t], L, R) and fin(S | 1 << t, cnt + 1):
                r = True
                break
        memo[S] = r
        return r

    res = set()
    for t in range(1, q + 1):
        if t != t0 and fin(1 << t, 1):
            res.add(t)
            res.add(sg[t])
    return res


def exc(q, nu, s):
    return q & (q - 1) != 0 and ((nu == 1 and s == 1) or (nu + 1 == q and s == q))


if __name__ == '__main__':
    for q in range(int(sys.argv[1]), int(sys.argv[2]) + 1, 2):
        for nu in range(q):
            r = starts(q, nu)
            miss = [t for t in range(1, q + 1) if not exc(q, nu, t) and t not in r]
            print(q, nu, 'palindromic starts', sorted(r), 'missing', miss)

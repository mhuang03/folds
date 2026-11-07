# agree.py: exceptional pairs of the maps of Theorem R (q = 2m+1, nu = 2w), in the sense of
# Live4.Agree: (i, j) is exceptional for phi if the window relation of j to i in the k-strip
# differs from that of phi(j) to phi(i) in the Q-strip.
import sys


def reach(n, t):
    return min(t - 1, n - t)


def agree(Q, k, phi, i, j):
    a = (phi(i) - reach(Q, phi(i)) <= phi(j) < phi(i)) == (i - reach(k, i) <= j < i)
    b = (phi(i) < phi(j) <= phi(i) + reach(Q, phi(i))) == (i < j <= i + reach(k, i))
    return a and b


def exc(Q, k, phi):
    return [(i, j) for i in range(1, k + 1) for j in range(1, k + 1) if i != j and not agree(Q, k, phi, i, j)]


if __name__ == '__main__':
    for m in range(3, 12):
        q = 2 * m + 1
        for w in range(0, m):
            psi = lambda y: 2 * y if y <= w else 2 * y - 1      # sig o odd-embedding, (m+1)-strip
            chi = lambda z: 2 * z - 1 if z <= w else 2 * z      # sig o even-embedding, m-strip
            odd = lambda i: 2 * i - 1
            ev = lambda j: 2 * j
            assert not exc(q, m + 1, odd) and not exc(q, m, ev)
            print(f'm={m} w={w} psi:{exc(q, m + 1, psi)} chi:{exc(q, m, chi)}')

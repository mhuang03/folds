"""excpairs.py m: NotAgree pairs of psiW w (on the (m+1)-strip) and chiW w (on the m-strip) inside
Q = 2m+1, for every w < m, as in Folds/SuperExp8.lean (goodL_oddR).  A pair (i, j) means
"i before j" in sig o alpha (resp. sig o beta)."""
import sys


def reach(N, x):
    return min(x - 1, N - x)


def agree(Q, k, f, i, j):
    fi, fj = f(i), f(j)
    l1 = fi - reach(Q, fi) <= fj < fi
    r1 = i - reach(k, i) <= j < i
    l2 = fi < fj <= fi + reach(Q, fi)
    r2 = i < j <= i + reach(k, i)
    return l1 == r1 and l2 == r2


m = int(sys.argv[1])
Q = 2 * m + 1
for w in range(0, m):
    psi = lambda y: 2 * y if y <= w else 2 * y - 1
    chi = lambda z: 2 * z - 1 if z <= w else 2 * z
    P = [(i, j) for i in range(1, m + 2) for j in range(1, m + 2) if i != j and not agree(Q, m + 1, psi, i, j)]
    C = [(i, j) for i in range(1, m + 1) for j in range(1, m + 1) if i != j and not agree(Q, m, chi, i, j)]
    print('w=%d psi:%s chi:%s' % (w, P, C))

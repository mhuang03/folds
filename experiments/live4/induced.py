"""induced.py k r: for q = 2k+1, nu = 4r+1, the transversal X = {2i : i <= r} + {2i+1 : i > r}
of the palindromic chains (palsets.py).  Prints, per index i, how the window relation of
phi(i) inside X (in the q-strip) differs from the window of i in the k-strip: extra / missing
indices on the left and right.  Same for sig(X) = psi([k]) (psi(i) = 2i-1, i <= r; 2i, i > r)."""
import sys

k, r = int(sys.argv[1]), int(sys.argv[2])
q = 2 * k + 1


def reach(N, m):
    return min(m - 1, N - m)


def show(name, phi):
    print(name, [phi(i) for i in range(1, k + 1)])
    for i in range(1, k + 1):
        x = phi(i)
        rq = reach(q, x)
        Lq = {j for j in range(1, k + 1) if x - rq <= phi(j) < x}
        Rq = {j for j in range(1, k + 1) if x < phi(j) <= x + rq}
        rk = reach(k, i)
        Lk = set(range(i - rk, i))
        Rk = set(range(i + 1, i + rk + 1))
        d = (sorted(Lq - Lk), sorted(Lk - Lq), sorted(Rq - Rk), sorted(Rk - Rq))
        if any(d):
            print('  i', i, 'L+', d[0], 'L-', d[1], 'R+', d[2], 'R-', d[3])


show('X', lambda i: 2 * i if i <= r else 2 * i + 1)
show('sigX', lambda i: 2 * i - 1 if i <= r else 2 * i)

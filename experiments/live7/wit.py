"""wit.py N u u': all Beatty witnesses (orientation, p, h, index of u-side element a, b = number of
elements after the v-side element) of the pair (u, N + 1 - u')."""
import sys
sys.path.insert(0, '../live6')
from ucov import dead


def idx(N, p, h, x):
    """index of x in X(N, p, h) or 0"""
    if (p * (x + 1) + h - 1) % N <= p - 1:
        return (p * (x + 1) + h - 1) // N
    return 0


def witnesses(N, u, up):
    v = N + 1 - up
    out = []
    for p in range(2, (N + 1) // 2 + 1):
        for h in (0, 1):
            if h + 2 * p > N + 1:
                continue
            for o, (x, y) in (('R', (u, v)), ('L', (up, N + 1 - u))):
                a, b = idx(N, p, h, x), idx(N, p, h, y)
                if a and b and not dead(p, a, b):
                    out.append((o, p, h, a, p - b))
    return out


if __name__ == '__main__':
    N, u, up = map(int, sys.argv[1:4])
    for w in witnesses(N, u, up):
        print(w, 'theta=%.4f' % (w[1] / N))

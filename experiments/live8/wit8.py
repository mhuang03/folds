"""wit8.py: witnesses of the wide pairs.  pair (u, u') means (u, v = N+1-u'), u <= u',
u + 2u' <= N - 1.  Families: X(N,p,h) = {floor((rN-h)/p)}, Z(N,p) = {floor(k(N+2)/(p+1))}."""
import sys


def dead(n, a, b):
    return a == 1 and b == n and ((n % 2 == 0 and n >= 4) or n == 7)


def idxX(N, p, h, x):
    t = p * (x + 1) + h - 1
    if 1 <= x <= N and t % N <= p - 1:
        return t // N
    return 0


def idxZ(N, p, x):
    M, q = N + 2, p + 1
    r = (-(q * x)) % M
    if 1 <= x <= N and r <= q - 1:
        return (q * x + r) // M
    return 0


def witnesses(N, u, v, fams='XZ'):
    out = []
    for orient, (x, y) in enumerate([(u, v), (N + 1 - v, N + 1 - u)]):
        if 'X' in fams:
            for p in range(1, (N + 1) // 2 + 1):
                for h in (0, 1):
                    if h + 2 * p > N + 1:
                        continue
                    a, b = idxX(N, p, h, x), idxX(N, p, h, y)
                    if a and b and a < b and not dead(p, a, b):
                        out.append((orient, 'X%d' % h, p, a, b))
        if 'Z' in fams:
            for p in range(1, N // 2 + 1):
                a, b = idxZ(N, p, x), idxZ(N, p, y)
                if a and b and a < b and not dead(p, a, b):
                    out.append((orient, 'Z', p, a, b))
    return out


def wide(N):
    for u in range(1, N):
        for up in range(u, N):
            if u + 2 * up > N - 1:
                break
            yield u, up


if __name__ == '__main__':
    N = int(sys.argv[1])
    K = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    for u, up in wide(N):
        v = N + 1 - up
        if (u + v) % 2 == 0:
            continue
        w = witnesses(N, u, v)
        if len(w) <= K:
            print(u, up, len(w), w)

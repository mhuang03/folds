"""ydefects.py N1 N2: for each Beatty copy X(N,p,g), the copy defects of its complement
Y = {y_1 < ... < y_q}: indices j with c~_Y(2 y_j - 1) != 2j - 1 (and the value found)."""
import sys


def defects(N, Y):
    Y = sorted(Y)
    q = len(Y)
    S = set(Y)
    c = [0] * (N + 1)
    for y in range(1, N + 1):
        c[y] = c[y - 1] + (y in S)

    def ct(t):
        return c[t] if t <= N else q + c[t - N]
    return [(j + 1, y, ct(2 * y - 1) - (2 * j + 1)) for j, y in enumerate(Y) if ct(2 * y - 1) != 2 * j + 1]


if __name__ == '__main__':
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        seen = set()
        for p in range(2, N):
            for g in range(2 * p - 1 - N, 1):
                X = tuple((r * N + g) // p for r in range(1, p + 1))
                if X in seen:
                    continue
                seen.add(X)
                Y = sorted(set(range(1, N + 1)) - set(X))
                d = defects(N, Y)
                print(N, p, g, 'q=%d' % len(Y), 'ndef=%d' % len(d), d)

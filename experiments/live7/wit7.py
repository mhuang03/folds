"""wit7.py N u u': all Beatty (R/L, h) and TB (T/T' = mirror) witnesses of the pair (u, N + 1 - u')."""
import sys
sys.path.insert(0, '../live6')
from ucov import dead
from wit import witnesses as bwit


def tb_witnesses(N, u, up):
    M = N + 2
    out = []
    for p in range(1, N // 2 + 1):
        q = p + 1
        # T: u = floor(iM/q), u' = floor((jM - 1)/q)
        for o, (x, y) in (('T', (u, up)), ("T'", (up, u))):
            # x = floor(iM/q)  <=>  (-x q) mod M <= q - 1 ; i = (x q + r)/M
            r = (-x * q) % M
            if r > q - 1:
                continue
            i = (x * q + r) // M
            s = (-y * q - 1) % M   # y = floor((jM - 1)/q) <=> jM - 1 - yq in [0, q-1]
            if s > q - 1:
                continue
            j = (y * q + 1 + s) // M
            if i >= 1 and j >= 1 and i + j <= p and not dead(p, i, p + 1 - j):
                out.append((o, p, i, j))
    return out


if __name__ == '__main__':
    N, u, up = map(int, sys.argv[1:4])
    for w in bwit(N, u, up):
        print(w, 'theta=%.4f' % (w[1] / N))
    for w in tb_witnesses(N, u, up):
        print(w, 'theta=%.4f' % ((w[1] + 1) / (N + 2)))

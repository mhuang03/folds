"""census.py S A: valid mixed vertices grouped by (u, j): u = (q z_a)^(-1) mod q (centered), j the
attachment index; V = number of valid time orders, M(u,j)/M(1,0) the modulus ratio (formula of
PROOFS.txt section 2, checked against the computed terms)."""
import sys, math
from fractions import Fraction as Fr
from mixed import valid_vertices, word


def modulus(u, j, s, a):
    D = 2 ** s - 1
    q = 2 ** a * D
    L = -math.log(q)
    for l in range(1, a + 1):
        L -= math.log(2 * abs(math.sin(math.pi * u / 2 ** l)))
    for e in range(s):
        L -= math.log(2 * abs(math.sin(math.pi * u * 2 ** e / q)))
    L -= math.log(2 * abs(math.sin(math.pi * u * 2 ** (s - j) / q)))
    return math.exp(L)


def ujof(V, s, a):
    q = V['q']
    N = int(V['z'][-1] * q)
    u = pow(N, -1, q)
    if u > q // 2:
        u -= q
    return u, V['j']


if __name__ == '__main__':
    s, a = int(sys.argv[1]), int(sys.argv[2])
    groups = {}
    for V in valid_vertices(s, a):
        u, j = ujof(V, s, a)
        m = modulus(u, j, s, a)
        assert abs(abs(V['term']) - m) < 1e-9 * max(1, m), (abs(V['term']), m)
        key = (abs(u), j)
        g = groups.setdefault(key, [0, 0, set()])
        g[0] += 1
        g[1] += V['term']
        g[2].add(word(V['lab']))
    M0 = modulus(1, 0, s, a)
    tot = sum(g[1] for g in groups.values())
    print(f'(s,a)=({s},{a}) q={2**a*(2**s-1)}  M(1,0)={M0:.6g}  total={tot:.6g} |total|/M0={abs(tot)/M0:.6g}')
    rest = 0
    for key in sorted(groups, key=lambda kk: -modulus(kk[0], kk[1], s, a)):
        g = groups[key]
        r = modulus(key[0], key[1], s, a) / M0
        if key != (1, 0):
            rest += g[0] * r
        if r > 1e-4 or key == (1, 0):
            print(f'  |u|={key[0]:5d} j={key[1]:2d} V={g[0]:4d} ratio={r:.4g}  sum/M0={abs(g[1])/M0:.4g}  words={sorted(g[2])[:4]}')
    print(f'  rest bound sum V*ratio (u,j) != (1,0): {rest:.4g}')

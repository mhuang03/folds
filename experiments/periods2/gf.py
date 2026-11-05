"""gf.py K: the REDUCED rational generating function F_K(t) = sum_N T(N,K) t^N (sum of the
Normaliz class series of ../prefix5/classes_K.json), its denominator factored into cyclotomic
polynomials Phi_q^{e_q}, and a comparison with the prediction  e_q = K + 1 - m(q),
m(q) = least m such that q divides a single 2^a(2^s - 1) (s >= 0) with a + s <= m - 1
(m(1) = 0; Theorem B / the staircase).  Exact (sympy)."""
import sys
import json
import sympy as sp
from sympy import cyclotomic_poly as Phi

t = sp.symbols('t')


def m_of(q):
    if q == 1:
        return 0
    m = 1
    while True:
        terms = [2 ** (m - 1)] + [2 ** (m - 1 - s) * (2 ** s - 1) for s in range(1, m)]
        if any(T % q == 0 for T in terms):
            return m
        m += 1


def F(K, path=None):
    path = path or f'../prefix5/classes_{K}.json'
    tot = 0
    groups = {}
    for line in open(path):
        cl = json.loads(line)
        key = tuple(sorted(cl['den']))
        num = sum(c * t ** i for i, c in enumerate(cl['num'])) * t ** cl['shift']
        groups[key] = groups.get(key, 0) + num
    for key, num in groups.items():
        den = sp.Integer(1)
        for d in key:
            den *= (1 - t ** d)
        tot += sp.Poly(sp.expand(num), t).as_expr() / den
    return sp.cancel(sp.together(tot))


if __name__ == '__main__':
    K = int(sys.argv[1])
    G = F(K)
    num, den = sp.fraction(G)
    den = sp.Poly(den, t)
    fac = {}
    rest = den
    q = 1
    while rest.degree() > 0 and q < 400:
        P = sp.Poly(Phi(q, t), t)
        e = 0
        while True:
            Qt, R = sp.div(rest, P)
            if R.is_zero:
                rest = Qt
                e += 1
            else:
                break
        if e:
            fac[q] = e
        q += 1
    pred = {}
    for q in range(1, 400):
        mq = m_of(q)
        if mq <= K:
            pred[q] = K + 1 - mq
    print(f'K={K}: reduced denominator = prod Phi_q^e_q with')
    print('   ', sorted(fac.items()))
    print('   prediction e_q = K+1-m(q):', sorted(pred.items()))
    print('   equal:', fac == pred, '  numerator degree', sp.Poly(num, t).degree(),
          ' denominator degree', den.degree())
    print('   differences:', {q: (fac.get(q), pred.get(q)) for q in set(fac) | set(pred)
                              if fac.get(q) != pred.get(q)})

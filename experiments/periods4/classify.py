"""classify.py KMAX [KMIN]: exhaustive enumeration of ALL valid cycle + pendant chain vertices for
the mixed orders q = 2^a (2^s - 1), a + s = k - 1, a >= 1, s >= 2, KMIN <= k <= KMAX, and checks:
  (i)   every valid vertex has |term| = M(u, j) (closed-form modulus, Lemma 1.3);
  (ii)  V(u, j) <= C(s - j + a, a) (Lemma 1.4);
  (iii) Lemma 2.3: for s >= 3 the valid time orders of the main structure (u = +-1, j = 0) are
        exactly c^s followed by the chain with the closing point after p = 0..min(a,2) of the
        chain points;
  (iv)  Lemma 2.4: for s >= 4 no structure with u = +-1 mod D and j >= 1 is valid;
and prints the exact total (coefficient of e(-N/q) in c_0(T(N,k))) and its ratio to M(1,0)."""
import sys
import math
from math import comb
from mixed import valid_vertices, word
from census import modulus, ujof

K = int(sys.argv[1])
K0 = int(sys.argv[2]) if len(sys.argv) > 2 else 4
allok = True
for k in range(K0, K + 1):
    for s in range(2, k - 1):
        a = k - 1 - s
        D = 2 ** s - 1
        q = 2 ** a * D
        V = {}
        tot = 0
        n = 0
        ok = True
        mainwords = set()
        for X in valid_vertices(s, a):
            n += 1
            u, j = ujof(X, s, a)
            m = modulus(u, j, s, a)
            ok &= abs(abs(X['term']) - m) <= 1e-9 * m
            V[(u, j)] = V.get((u, j), 0) + 1
            tot += X['term']
            if abs(u) == 1 and j == 0:
                mainwords.add(word(X['lab']))
            if s >= 4 and j >= 1 and (u % D in (1, D - 1)):
                ok = False
        ok &= all(v <= comb(s - j + a, a) for (u, j), v in V.items())
        if s >= 3:
            want = {'c' * s + 'z' * p + 'c' + 'z' * (a - p) for p in range(min(a, 2) + 1)}
            ok &= mainwords == want
        allok &= ok
        M0 = modulus(1, 0, s, a)
        print(f'k={k:2d} s={s:2d} a={a:2d} q={q:6d}: {n:6d} valid vertices, {len(V):5d} structures; '
              f'coefficient = {tot.real:+.10g} {tot.imag:+.10g}i, |coef|/M(1,0) = {abs(tot) / M0:.6f}  '
              f'{"ok" if ok else "CHECK FAILED"}', flush=True)
print('ALL CHECKS PASSED' if allok else 'SOME CHECK FAILED')

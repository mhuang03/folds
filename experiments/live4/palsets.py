"""palsets.py q nu: the transversal SETS X of palindromic chains (see palnu.py) for (q, nu),
q odd, with the starts each admits.  Forward subset DP."""
import sys
from palnu import win, bal

q, nu = int(sys.argv[1]), int(sys.argv[2])
L, R = win(q)
sg = [0] + [(nu - t) % q + 1 for t in range(1, q + 1)]
t0 = [t for t in range(1, q + 1) if sg[t] == t][0]
k = (q - 1) // 2


def sgset(S):
    T = 0
    for t in range(1, q + 1):
        if S >> t & 1:
            T |= 1 << sg[t]
    return T


# layer DP: map set -> set of possible first elements
layer = {0: set()}
for c in range(k):
    nxt = {}
    for S, st in layer.items():
        T = sgset(S)
        for t in range(1, q + 1):
            if t == t0 or (S >> t & 1) or (T >> t & 1):
                continue
            if bal(S, t, L, R) and bal(T, sg[t], L, R):
                S2 = S | 1 << t
                nxt.setdefault(S2, set()).update(st if S else {t})
    layer = nxt
full = {S: st for S, st in layer.items() if bal(S, t0, L, R)}
print('q', q, 'nu', nu, 't0', t0, 'number of sets', len(full))
for S, st in sorted(full.items(), key=lambda x: -len(x[1]))[:40]:
    X = [t for t in range(1, q + 1) if S >> t & 1]
    print(X, 'starts', sorted(st))

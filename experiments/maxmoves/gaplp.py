"""gaplp.py -- continuum gap bound.  With circle gaps gamma_0 (the gap through 0) .. gamma_{s-1},
the zero set of G = F(2t) - 2F(t) has measure <= gamma_0/2 + sum_{k=1}^{s-1} min(gamma_k, gamma_{2k mod s}/2).
Maximise this upper bound by LP for each s."""
import numpy as np
from scipy.optimize import linprog
for s in range(1, 17):
    n = s + (s - 1)
    c = np.zeros(n); c[0] = -0.5; c[s:] = -1
    A = []; b = []
    for k in range(1, s):
        r = np.zeros(n); r[s + k - 1] = 1; r[k] -= 1; A.append(r); b.append(0)
        r = np.zeros(n); r[s + k - 1] = 1; r[(2 * k) % s] -= 0.5; A.append(r); b.append(0)
    Aeq = np.zeros((1, n)); Aeq[0, :s] = 1
    res = linprog(c, A_ub=np.array(A) if A else None, b_ub=b if b else None,
                  A_eq=Aeq, b_eq=[1], bounds=[(0, None)] * n)
    print(s, round(-res.fun, 6), np.round(res.x[:s], 4))

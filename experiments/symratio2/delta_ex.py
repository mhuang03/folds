"""delta_ex.py -- examples of window pairs with Delta != 0 (random 6-tuples), showing the
boundary cells: A-cells (k,i) with 2y_k - u_i in {0,1,L,L+1}, B-cells with 2u_i - y_k in it."""
import sys
import numpy as np
from delta import pi_gh, V

L = int(sys.argv[1]); seed = int(sys.argv[2]) if len(sys.argv) > 2 else 0
rng = np.random.default_rng(seed)
shown = 0
while shown < 6:
    D = np.array([rng.choice(np.arange(1, L + 1), 6, replace=False) for _ in range(2000)], dtype=np.int32)
    C = np.array([rng.choice(np.arange(1, L + 1), 6, replace=False) for _ in range(1)], dtype=np.int32)
    P = pi_gh(L, D, C)
    dl = P.astype(float) @ V
    for s in np.nonzero(dl[:, 0])[0][:2]:
        y, u = D[s], C[0]
        A = [(k + 1, i + 1, 2 * y[k] - u[i]) for k in range(6) for i in range(6) if 2 * y[k] - u[i] in (0, 1, L, L + 1)]
        B = [(k + 1, i + 1, 2 * u[i] - y[k]) for k in range(6) for i in range(6) if 2 * u[i] - y[k] in (0, 1, L, L + 1)]
        print("y'=", y.tolist(), "u=", u.tolist(), "Delta=", int(dl[s, 0]), "F(g,h)=", P[s, 0].reshape(3, 3).tolist())
        print("   A-ties (k,i,K):", A, " B-ties (k,i,K'):", B)
        shown += 1

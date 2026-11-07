"""delta_rand.py -- Delta(Pi^{.}_L(S,T)) for random 6-tuples (distinct entries, values in [1,L]).
Is Delta = 0 for every pair when 3 | L, also for windows that are not windows of a 3-AP-free
permutation?  Prints, per L, the number of pairs with Delta != 0 and the values seen."""
import sys
import numpy as np
from delta import pi_gh, V

rng = np.random.default_rng(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
n = 400
for L in list(range(8, 40)) + [48, 60, 61, 62, 96, 97, 98]:
    D = np.array([rng.choice(np.arange(1, L + 1), 6, replace=False) for _ in range(n)], dtype=np.int32)
    C = np.array([rng.choice(np.arange(1, L + 1), 6, replace=False) for _ in range(n)], dtype=np.int32)
    dl = pi_gh(L, D, C).astype(float) @ V
    nz = dl != 0
    print(L, L % 3, nz.sum(), sorted(set(dl[nz].astype(int).tolist()))[:10], flush=True)

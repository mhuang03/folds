"""table.py KMIN KMAX: max over s of the bound U(s, a) = U_alpha + U_I + U_II (bound.py), per k."""
import sys
from bound import U_alpha, U_I, U_II

k0, k1 = int(sys.argv[1]), int(sys.argv[2])
for k in range(k0, k1 + 1):
    best = (0, None)
    for s in range(4, k - 2):
        a = k - 1 - s
        u = (U_alpha(s, a), U_I(s, a), U_II(s, a))
        if sum(u) > best[0]:
            best = (sum(u), (s, a), u)
    print(f'k={k}: max U = {best[0]:.4g} at (s,a)={best[1]}  (alpha, I, II) = '
          f'({best[2][0]:.3g}, {best[2][1]:.3g}, {best[2][2]:.3g})', flush=True)

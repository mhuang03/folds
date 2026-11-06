"""contopt.py -- continuum maximum of the valid measure |{t : F(2t) = 2F(t)}| over s-point sets
in (0,1) (F = counting function, F(t+1) = F(t) + s), by random restarts + Nelder-Mead.
Exact objective: sum_k |(x_k, x_{k+1}) cap (y_{2k}/2, y_{2k+1}/2)|.  usage: python3 contopt.py s"""
import sys, random
import numpy as np
from scipy.optimize import minimize

def zmeasure(xs):
    s = len(xs)
    x = sorted(min(max(v, 1e-12), 1 - 1e-12) for v in xs)
    # breakpoints of F on [0, 2]: y_0 = 0, y_1..y_s = x, y_{s+1}..y_{2s} = 1 + x, y_{2s+1} = 2
    y = [0.0] + x + [1 + v for v in x] + [2.0]
    J = [0.0] + x + [1.0]               # F = k on (J[k], J[k+1]) for t in (0,1)
    tot = 0.0
    for k in range(s + 1):
        lo = max(J[k], y[2 * k] / 2); hi = min(J[k + 1], y[2 * k + 1] / 2)
        tot += max(0.0, hi - lo)
    return tot

s = int(sys.argv[1]); random.seed(1)
best = (0, None)
for it in range(400):
    x0 = np.array(sorted(random.random() for _ in range(s)))
    r = minimize(lambda v: -zmeasure(v), x0, method="Nelder-Mead",
                 options={"xatol": 1e-10, "fatol": 1e-12, "maxiter": 20000})
    if -r.fun > best[0]:
        best = (-r.fun, sorted(r.x))
print("s=%d sup ~ %.6f at %s" % (s, best[0], np.round(best[1], 5)))

"""Large-N behaviour of the Gaussian resummation y_G(N) = log E[det(Gamma o B)^(-1/2)]."""
import sys
import numpy as np
from gauss_mc import gram, logmean_detinvsqrt

rng = np.random.default_rng(2)
S = int(sys.argv[1]) if len(sys.argv) > 1 else 4000
for N in (33, 40, 41, 60, 61, 80, 81, 120, 121, 160, 161):
    lm, err, ml = logmean_detinvsqrt(gram(N), S, rng, batch=100)
    print("%4d yG=%.3f (%.3f)  E[-logdet/2]=%.3f  yG/N=%.4f  yG/(N logN)=%.4f" % (
        N, lm, err, ml, lm / N, lm / (N * np.log(N))), flush=True)

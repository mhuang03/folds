"""biastab.py: octave means of the continuum SMC (p_k and int F^2 in parentheses) for several
population sizes M, and the 1/M extrapolation p(inf) ~ p(M) + (p(M) - p(M/4))/3 from the two
largest M available for that octave."""
import numpy as np


def load(f):
    d = {}
    for l in open(f):
        p = l.split()
        if len(p) >= 5:
            d[int(p[0])] = (float(p[1]), float(p[4]))
    return d


R = {1000: load('runs/cont_1024_1000_s41.txt'), 4000: load('runs/cont_K2600_M4000_s11.txt'),
     16000: load('runs/cont_1024_16000_s21.txt'), 64000: load('runs/cont_512_64000_s31.txt')}
for lo in [8, 16, 32, 64, 128, 256, 512]:
    ks = range(lo, min(2 * lo, 1024))
    row = [(M, np.mean([d[k][0] for k in ks]), np.mean([d[k][1] for k in ks]))
           for M, d in R.items() if max(d) >= max(ks)]
    ext = row[-1][1] + (row[-1][1] - row[-2][1]) / 3
    print(f'[{lo},{2*lo})', ' '.join(f'M={M}: {p:.5f} ({s:.2f})' for M, p, s in row),
          f' extrap {ext:.5f}')

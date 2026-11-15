"""Part 5: the averaged permutation matrix ("permuton") of V_N.
Reads data/permuton_<N>.txt (C[k][m] = #{a in V_N : a_k = m}) and prints density tables
N^2 C[k][m] / a(N) (uniform = 1), block-averaged to a 6 x 6 grid for N divisible by 6,
the symmetries, and a comparison of the rows with the first-panel law
h(x) = (3/sqrt 2) sqrt(min(x, 1-x)).
"""
import os
from math import sqrt
from fractions import Fraction
from common import HERE


def load(N):
    with open(os.path.join(HERE, 'data', f'permuton_{N}.txt')) as f:
        return [[int(v) for v in line.split()] for line in f if line.strip()]


def main():
    for N in (12, 13, 14, 20, 24):
        C = load(N)
        tot = sum(C[0])
        assert all(sum(r) == tot for r in C) and all(sum(C[k][m] for k in range(N)) == tot for m in range(N))
        mir = all(C[k][m] == C[k][N - 1 - m] for k in range(N) for m in range(N))
        rev = all(C[k][m] == C[N - 1 - k][m] for k in range(N) for m in range(N))
        tr = all(C[k][m] == C[m][k] for k in range(N) for m in range(N))
        print(f"N={N} a(N)={tot}  mirror-symmetric (m -> N+1-m): {mir}  reversal-symmetric (k -> N+1-k): {rev}  "
              f"transpose-symmetric (inverse): {tr}")
        dens = [[N * C[k][m] / tot for m in range(N)] for k in range(N)]
        mx = max(max(r) for r in dens); mn = min(min(r) for r in dens)
        print(f"  density range: {mn:.3f} .. {mx:.3f};  zero entries: {sum(1 for r in C for v in r if v == 0)}")
        if N <= 14:
            print("  density N*P(a_k = m), rows k = 1..ceil(N/2), columns m = 1..ceil(N/2):")
            for k in range((N + 1) // 2):
                print("   ", " ".join(f"{dens[k][m]:5.2f}" for m in range((N + 1) // 2)))
        if N % 6 == 0:
            b = N // 6
            print("  6 x 6 block averages (rows = time sextile, columns = panel sextile):")
            for i in range(6):
                print("   ", " ".join(f"{sum(dens[k][m] for k in range(i*b,(i+1)*b) for m in range(j*b,(j+1)*b))/(b*b):5.3f}"
                                      for j in range(6)))
        # rows versus the first-panel law
        h = [3 / sqrt(2) * sqrt(min((m + 0.5) / N, 1 - (m + 0.5) / N)) for m in range(N)]
        for k in (0, 1, N // 4, N // 2 - 1):
            tv = sum(abs(dens[k][m] - h[m]) for m in range(N)) / (2 * N)
            tvu = sum(abs(dens[k][m] - 1) for m in range(N)) / (2 * N)
            print(f"  step {k+1}: TV distance to sqrt-law {tv:.3f}, to uniform {tvu:.3f}")
        # time law of a fixed panel (columns)
        for m in (0, 1, N // 4, N // 2 - 1):
            col = [dens[k][m] for k in range(N)]
            print(f"  panel {m+1}: time density at steps 1, N/4, N/2: {col[0]:.3f} {col[N//4]:.3f} {col[N//2-1]:.3f}"
                  f"  (max {max(col):.3f}, min {min(col):.3f})")
        print()


if __name__ == '__main__':
    main()

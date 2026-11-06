"""probe3.py F M0 M1: weights (A_above, A_below) of the 1/D orbit vertex and its rotations
2^i/D with F free points (F <= 2, via ../periods2/face.py), for M = M0..M1."""
import sys
import time
sys.path.insert(0, '../periods2')
from face import orbit, integrate

F, M0, M1 = map(int, sys.argv[1:4])
rots = int(sys.argv[4]) if len(sys.argv) > 4 else 0
for M in range(M0, M1 + 1):
    D = 2 ** (M - 1) - 1
    t0 = time.time()
    for i in range(0, rots + 1):
        v, bits = orbit(M, 2 ** i)
        Aa, Ab = integrate(v, bits, M + F)
        print(f'M={M} D={D} theta=2^{i}/D  A_ab={Aa} ({float(Aa):.6f})  A_be={Ab} ({float(Ab):.6f})'
              f'  Delta*D={float((Aa - Ab) * D):.4f}', flush=True)
    print(f'   [{time.time() - t0:.1f}s]', flush=True)

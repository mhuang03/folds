# explore12.py K N c...: {1, 2, c} (N = 1 mod 4, c even) through phi12 (the odd class with
# 3 -> 2, N = 2p - 1) with the panel of c - 1 (or c + 1) moved to c: irregular panels, and the
# first step list (<= K, bin/gk) after which the image satisfies Theorem G.
import sys, subprocess, os
from nb import *
K = sys.argv[1]; N = int(sys.argv[2])
p = (N + 1) // 2
for c in map(int, sys.argv[3:]):
    for g, d in (((c) // 2, 1), ((c + 2) // 2, -1)):
        phi = lambda y: 2 if y == 2 else (2 * y - 1 + d if y == g else 2 * y - 1)
        if not increasing(N, p, phi): continue
        ir = irregular(N, p, phi)
        img = sorted({phi(y) for y in range(1, p + 1)})
        out = subprocess.run([os.path.join(os.path.dirname(os.path.abspath(__file__)), 'bin', 'gk'),
                              str(N), K] + [str(x) for x in img], capture_output=True, text=True).stdout.strip()
        print(N, c, 'g', g, 'move', d, 'irregular', ir, out)
        sys.stdout.flush()

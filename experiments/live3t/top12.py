# top12.py K N...: {1, 2, N - 1} for N = 2 mod 4 through zA (Z(N, N/2 + 1)) with the panels
# 2 -> 2 and 2s + 1 -> 4s + 1 moved; irregular panels, imbalances of the image, and the
# shortest step list (<= K, bin/gk) after which the image satisfies Theorem G.
import sys, subprocess, os
from nb import *
K = sys.argv[1]
for N in map(int, sys.argv[2:]):
    s = N // 4; p = 2 * s + 2
    zA = lambda k: 2 * k - 1 if k <= s + 1 else 2 * k - 2
    phi = (lambda k: 2 if k == 2 else 4 * s + 1 if k == 2 * s + 1 else zA(k)) if not os.environ.get("TOP") else (lambda k: 2 if k == 2 else 4 * s + 1 if k == p else zA(k))
    ir = irregular(N, p, phi)
    img = sorted({phi(k) for k in range(1, p + 1)})
    imb = [(m, L(N, img, m) - R(N, img, m)) for m in range(1, N + 1) if m not in img and L(N, img, m) != R(N, img, m)]
    out = subprocess.run([os.path.join(os.path.dirname(os.path.abspath(__file__)), 'bin', 'gk'), str(N), K] + [str(x) for x in img], capture_output=True, text=True).stdout.strip()
    print(N, 'irregular', ir, 'imbalances', imb, out)
    sys.stdout.flush()

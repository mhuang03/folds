import sys
from crude import rest2
K = int(sys.argv[1]); K0 = int(sys.argv[2]) if len(sys.argv) > 2 else 7
for k in range(K0, K + 1):
    for s in range(4, k - 2):
        a = k - 1 - s
        t, b = rest2(s, a, top=3)
        print(f'k={k:2d} s={s:2d} a={a:2d} rest2={t:.4g}  top: ' + '; '.join(f'u={u} j={j} w={w:.3g}' for w, u, j, r in b), flush=True)

"""r2top.py S A [N]: the largest terms of rest2 (crude tail after Lemmas 2.3, 2.4)."""
import sys
from crude import rest2

s, a = int(sys.argv[1]), int(sys.argv[2])
q = 2 ** a * (2 ** s - 1)
D = 2 ** s - 1
t, best = rest2(s, a, top=int(sys.argv[3]) if len(sys.argv) > 3 else 20)
print(f'(s,a)=({s},{a}) q={q} rest2={t:.4g}')
for w, u, j, r in best:
    uc = u if u < q // 2 else u - q
    um = u % D
    um = um if um < D // 2 else um - D
    y = u % 2 ** a
    y = y if y < 2 ** (a - 1) else y - 2 ** a
    print(f'  u={uc:9d}  u mod D={um:7d}  u mod 2^a={y:5d}  j={j:2d}  ratio={r:.3g}  C*ratio={w:.3g}')

"""List the tau in V_n with G(tau) ⊇ odds (every odd k before q(k) = 2k mod* n),
grouped by parity word; show the non-parity-block ones.  Usage: python3 godd.py n [show]"""
import sys
from collections import Counter
from eslip import gen
n = int(sys.argv[1]); show = int(sys.argv[2]) if len(sys.argv) > 2 else 40
V = gen(n)
def ms(x): return (x - 1) % n + 1
res = []
for t in V:
    pos = {m: i for i, m in enumerate(t)}
    if all(pos[k] < pos[ms(2 * k)] for k in range(1, n, 2)):
        res.append(t)
pb = [t for t in res if all(x % 2 == 1 for x in t[:n // 2])]
print("G ⊇ odds:", len(res), " parity blocks:", len(pb))
C = Counter(''.join('o' if x % 2 else 'e' for x in t) for t in res)
for w, c in C.most_common(30): print(w, c)
for t in [t for t in res if t not in pb][:show]: print(t)

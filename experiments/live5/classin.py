"""classin.py N1 N2 [qmax]: which residue classes C_s (mod q) of [N] satisfy the inward
criterion (Theorem G), so that they are co-reachable window copies (weak split) without a
residue chain."""
import sys
from zeroset import inward_set

qmax = int(sys.argv[3]) if len(sys.argv) > 3 else 9
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    row = []
    for q in range(2, qmax + 1):
        ss = [s for s in range(1, q + 1)
              if inward_set(N, set(range(s, N + 1, q)))]
        row.append(f'{q}:{"".join(str(s % 10) for s in ss) or "-"}')
    print(N, ' '.join(row))

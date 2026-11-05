"""Block projections by quantile.  Level j, blocks B_y = [2^j y, 2^j (y+1) - 1], y = 1..M_j - 1,
ordered by the time their q-th element is placed (q = 1..2^j).  Check des(d) >= lg(M_j) - 1 and
LDS(d) >= lg(M_j), and the chain des(d_j) >= des(d_{j+1}) + 1 for chosen quantile rules."""
from common import *
import sys
from collections import Counter
def proj(a, M, j, q):
    Mj = M >> j; cnt = Counter(); d = []
    for m in a:
        y = m >> j
        if 1 <= y <= Mj - 1:
            cnt[y] += 1
            if cnt[y] == q: d.append(y)
    return d
rules = {'first': lambda j: 1, 'last': lambda j: 1 << j, 'half': lambda j: (1 << j) // 2 or 1,
         'half+1': lambda j: (1 << (j - 1)) + 1 if j >= 1 else 1}
if __name__ == '__main__':
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        A = load(N); M = N + 1; J = lg(M)
        fails = Counter()
        for a in A:
            a = list(a)
            for rn, rule in rules.items():
                ds = [proj(a, M, j, rule(j)) for j in range(J)]
                for j in range(J):
                    if des(ds[j]) < lg(M >> j) - 1: fails[(rn, 'desbound', j)] += 1
                    if lds(ds[j]) < lg(M >> j): fails[(rn, 'ldsbound', j)] += 1
                    if j + 1 < J and des(ds[j]) < des(ds[j+1]) + 1: fails[(rn, 'deschain', j)] += 1
        print(N, sorted(fails.items()), flush=True)

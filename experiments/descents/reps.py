"""For valid a on N, pairs {2y, 2y+1} (y = 1..N' = floor((N-1)/2)).  Does there exist a choice
of one representative per pair such that the representative subsequence (relabelled y) is
valid on N'?  Variant 'lr': pairs with an element in the last run must use the other element.
Also report which simple rules (first occurrence, last occurrence, even element, odd element)
work."""
from common import *
import sys, itertools
from collections import Counter
def check(N, a, choice, Np):
    # choice[y] = 0 -> 2y, 1 -> 2y+1
    reps = {2*y + choice[y-1]: y for y in range(1, Np+1)}
    d = [reps[m] for m in a if m in reps]
    return valid(Np, d)
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    A = load(N); Np = (N - 1)//2
    cnt = Counter()
    for a in A:
        a = list(a); pos = {m: i for i, m in enumerate(a)}
        p = len(a) - 1
        while p > 0 and a[p-1] < a[p]: p -= 1
        last = set(a[p:])
        anyok = False; anylr = False
        for ch in itertools.product((0, 1), repeat=Np):
            if check(N, a, ch, Np):
                anyok = True
                if all(not ((2*y + ch[y-1]) in last) for y in range(1, Np+1)):
                    anylr = True; break
        rules = {
            'first': tuple(0 if pos[2*y] < pos[2*y+1] else 1 for y in range(1, Np+1)),
            'last': tuple(1 if pos[2*y] < pos[2*y+1] else 0 for y in range(1, Np+1)),
            'even': tuple(0 for y in range(Np)), 'odd': tuple(1 for y in range(Np))}
        key = (anyok, anylr) + tuple(r for r, ch in rules.items() if check(N, a, ch, Np))
        cnt[key] += 1
    print(N, sorted(cnt.items(), key=lambda kv: -kv[1]))

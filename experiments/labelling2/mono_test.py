"""Monotonicity in N: from an admissible labelling on N+1, which single-panel deletions give an
admissible labelling on N (labels unchanged)?  usage: mono_test.py DIR t Nmax
reads DIR/all_{N}_{t}.txt (one labelling per line)."""
import sys
from collections import Counter

def adm(c):
    N = len(c)
    for m in range(N):
        r = min(m, N - 1 - m); v = c[m]
        if r and sum(c[x] <= v for x in range(m - r, m)) > sum(c[x] < v for x in range(m + 1, m + r + 1)):
            return False
    return True

D, t, Nmax = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
for N1 in range(3, Nmax + 1):
    try:
        L = [l.strip() for l in open(f'{D}/all_{N1}_{t}.txt') if l.strip() and l[0].isdigit()]
    except FileNotFoundError:
        continue
    none = 0; rules = Counter(); total = 0
    for s in L:
        c = list(map(int, s))
        if len(set(c)) < t: continue     # only labellings that use all t labels
        total += 1
        ok = [p for p in range(N1) if adm(c[:p] + c[p + 1:])]
        if not ok: none += 1; ex = s
        top = max(c); bot = min(c)
        cand = {
            'first': 0, 'last': N1 - 1,
            'lasttop': max(i for i in range(N1) if c[i] == top),
            'firsttop': min(i for i in range(N1) if c[i] == top),
            'firstbot': min(i for i in range(N1) if c[i] == bot),
            'lastbot': max(i for i in range(N1) if c[i] == bot),
        }
        for k, p in cand.items():
            if p in ok: rules[k] += 1
    print(f'N+1={N1} t={t}: {total} labellings, no deletion works for {none}', dict(rules),
          ('e.g. ' + ex) if none else '')

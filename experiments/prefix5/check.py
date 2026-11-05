"""check.py: compare the exact series T{5,6}_series.txt (from the Normaliz generating functions)
with independent counts from ../prefix/prefix.c (DFS + sweep; 'brute' = direct definition):
  brute5_1_60.txt, heldout5_*.txt, ../prefix/T5.txt, T5b.txt  (column 6 = T(N,5))
  brute6_1_*.txt, heldout6_*.txt, ../prefix/T6.txt            (column 7 = T(N,6))
and T(N,4) with the fitted formula of ../prefix/formulas.py."""
import glob
import sys
sys.path.insert(0, '../prefix')


def ser(k):
    return {int(l.split()[0]): int(l.split()[1]) for l in open(f'T{k}_series.txt')}


def rows(fn, col):
    for l in open(fn):
        t = l.split()
        if len(t) > col and t[0][0] in '0123456789':
            yield int(t[0]), int(t[col])


for k, files in [(5, ['brute5_1_60.txt'] + sorted(glob.glob('heldout5_*.txt')) +
                  ['../prefix/T5.txt', '../prefix/T5b.txt']),
                 (6, sorted(glob.glob('brute6_*.txt')) + sorted(glob.glob('heldout6_*.txt')) +
                  ['../prefix/T6.txt'])]:
    s = ser(k)
    for fn in files:
        ns = []
        for n, v in rows(fn, k):
            assert s[n] == v, (k, fn, n, s[n], v)
            ns.append(n)
        print(f'T(N,{k}) = series on {fn}: {len(ns)} values, N in {ns[:1]}..{ns[-1:]}'
              + (f' {ns}' if len(ns) < 10 else ''))

import formulas
s4 = ser(4)
assert all(formulas.T4(n) == v for n, v in s4.items())
print(f'T(N,4) fitted formula (../prefix/formulas.py) = exact series for N = 1..{max(s4)}')

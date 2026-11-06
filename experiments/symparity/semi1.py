"""Semi-symmetric sequences, odd N: E - O (even-first minus odd-first) = EE - OO, where
EE/OO = #(first and last both even/odd).  Breakdown by first panel and other refinements."""
import sys
from collections import Counter
from apfree import enum_semi

Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 11
for N in range(3, Nmax + 1, 2):
    L = enum_semi(N)
    E = sum(1 for w in L if w[0] % 2 == 0)
    O = len(L) - E
    pairs = Counter((w[0] % 2, w[-1] % 2) for w in L)
    print(f'N={N} a={len(L)} E-O={E - O}  OO={pairs[(1, 1)]} EE={pairs[(0, 0)]} OE={pairs[(1, 0)]}')
    # sequences with first,last same parity: by (first,last)
    same = Counter((w[0], w[-1]) for w in L if w[0] % 2 == w[-1] % 2)
    print('   same-parity (first,last) pairs:', sorted(same.items()))
    # balance by position
    bal = [sum(1 if w[k] % 2 == 0 else -1 for w in L) for k in range(N)]
    print('   even-odd by position:', bal)

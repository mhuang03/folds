"""diag.py N p e e' L: TB'' (slope (N+1)/(p+1)): print the set, the copy defects
(elements x with I(x) != 0) and the imbalance signs outside the set."""
import sys
sys.path.insert(0, '../live6')
from twoside import imb_all
from tb3 import tbx

N, p, e, e2, L = map(int, sys.argv[1:6])
X = tbx(N, p, e, e2, L)
ind, I = imb_all(N, X)
print(X)
print('copy defects', [(x, I[x]) for x in X if I[x]])
print('signs', ''.join('x' if ind[m] else ('-' if I[m] < 0 else '+' if I[m] > 0 else '0')
                       for m in range(1, N + 1)))

"""search.py FILE COL NMIN  then lines of candidate period specs per coefficient (top first),
given as python lists in the code below; prints the consistent specs with fewest unknowns."""
import itertools
import sys
from qfit import load, fit

d = load(sys.argv[1], int(sys.argv[2]))
nmin = int(sys.argv[3])
cands = eval(sys.argv[4])  # e.g. [['1'],['1','2'],['2+3','4+3'],['8+3+7','24+7']]
res = []
for spec in itertools.product(*cands):
    periods = [[int(u) for u in t.split('+')] for t in spec]
    nun = sum(sum(ps) - len(ps) + 1 for ps in periods)
    cons, uniq, sol, extra, idx = fit(d, periods, nmin)
    print(','.join(spec), 'unknowns', nun, 'consistent', cons, 'unique', uniq, 'checks', extra, flush=True)

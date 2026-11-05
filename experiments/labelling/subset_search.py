"""For each admissible labelling c on [N] with t labels, list the subsets T of size
N' = (N-1)//2 such that c restricted to T (order-preserving, as a strip of length N') is
admissible and uses at most t-1 distinct labels.  usage: subset_search.py file [maxshow]"""
import sys, itertools
from reduce_test import adm
f = sys.argv[1]; show = int(sys.argv[2]) if len(sys.argv) > 2 else 5
N, t = map(int, f.split('/')[-1][4:-4].split('_'))
Np = (N - 1) // 2
tot = 0; none = 0
for s in open(f):
    s = s.strip()
    if len(s) != N: continue
    c = [int(ch) for ch in s]
    good = []
    for T in itertools.combinations(range(N), Np):
        lab = [c[i] for i in T]
        if len(set(lab)) > t - 1: continue
        if adm([0] + lab): good.append(tuple(i + 1 for i in T))
    tot += 1
    if not good: none += 1
    if tot <= show or not good:
        print(s, len(good), good[:6])
print('N', N, 't', t, 'labellings', tot, 'with no good subset', none)

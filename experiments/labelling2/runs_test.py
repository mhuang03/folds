"""Candidate (A) of labelling/PROOFS.txt: maximal runs of labels < j.  For each j report the
maximal length of an inner run (not touching the right edge), of a run touching the right
edge, and of a run touching the left edge (but not the right one).
usage: runs_test.py file..."""
import sys
from collections import defaultdict
inner = defaultdict(int); right = defaultdict(int); leftr = defaultdict(int); ex = {}
for fn in sys.argv[1:]:
    for line in open(fn):
        s = line.strip()
        if not s[:1].isdigit(): continue
        c = list(map(int, s)); N = len(c)
        for j in range(1, max(c) + 1):
            i = 0
            while i < N:
                if c[i] < j:
                    k = i
                    while k < N and c[k] < j: k += 1
                    L = k - i
                    if k == N:
                        if L > right[j]: right[j] = L; ex['R', j] = s
                    else:
                        if L > inner[j]: inner[j] = L; ex['I', j] = s
                        if i == 0 and L > leftr[j]: leftr[j] = L
                    i = k
                else:
                    i += 1
for j in sorted(inner):
    print(f'j={j}: inner max {inner[j]} (bound 2^(j+1)-2 = {2**(j+1)-2}), left-edge max {leftr[j]}, right-edge max {right[j]}  e.g. {ex.get(("R", j))}')

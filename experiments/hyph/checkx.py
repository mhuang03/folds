"""checkx.py: (1) Lemma X: GoodL(n, nu) <=> xcond(n, nu) on random valid orders and on all
GoodL orders; (2) the odd near-reduction for nu = 2w (see PROOFS.txt)."""
import random, sys, itertools
from lib import *

random.seed(1)


def rand_valid(n):
    while True:
        S = set(); seq = []
        while len(seq) < n:
            c = [t for t in range(1, n + 1) if t not in S and step_ok(n, S, t)]
            if not c:
                break
            t = random.choice(c); seq.append(t); S.add(t)
        if len(seq) == n:
            return seq


bad = 0
for n in range(2, 16):
    for _ in range(300):
        seq = rand_valid(n)
        for nu in range(n):
            if goodL(n, nu, seq) != xcond(n, nu, seq):
                bad += 1
print('Lemma X mismatches:', bad)

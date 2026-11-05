"""Split slips on N = 3n (exploration, PROOFS.txt section 6).

Class order (1,3,2) of the residues mod 3 (composition theorem).  Type-B slips exchange
3i-2 (class 1) and 3i-1 (class 2).  Claim tested here: if the class-2 block is an
odds-first parity-block sequence, then ANY set of type-B slips at even i (2 <= i <= n)
keeps the sequence valid, for arbitrary valid class-1 and class-3 blocks.
Mode 'exh' (small n): all blocks, all slip sets.  Mode 'rand': random samples.
Modes 'randB' / 'slipB': the B part (classes 1, 3 = the doubling-split copy of the 2n-strip)
is a random valid sequence / a random reversed slip sequence of the 2n-strip instead of the
parity block (class 1, class 3); then the claim FAILS.
"""
import random
import sys
from itertools import combinations, product
sys.path.insert(0, __file__.rsplit('/', 1)[0])
from chaincheck import V, valid_seq, valid_step, PB, okF, okS, slip


def build(b1, b3, b2, DB):
    sw = {}
    for i in DB:
        x, y = 3 * i - 2, 3 * i - 1
        sw[x], sw[y] = y, x
    seq = []
    for c, b in ((1, b1), (3, b3), (2, b2)):
        seq += [sw.get(3 * (j - 1) + c, 3 * (j - 1) + c) for j in b]
    return seq


def rand_valid(n):
    while True:
        S, seq = set(), []
        for _ in range(n):
            c = [m for m in range(1, n + 1) if m not in S and valid_step(S, m, n)]
            if not c:
                break
            m = random.choice(c); S.add(m); seq.append(m)
        if len(seq) == n:
            return seq


def rand_slip(n, Vn):
    while True:
        t, s_ = random.choice(Vn), random.choice(Vn)
        D = [k for k in range(1, n) if okF(t, [k], n) and okS(s_, [k], n) and random.random() < 0.7]
        if D:
            return list(reversed(slip(set(D), t, s_, n)))


def mainB(mode, n, T):
    N = 3 * n
    random.seed(5)
    Vn = V(n)
    Bpan = sorted(x for x in range(1, N + 1) if x % 3 != 2)
    pbs = [PB(a, b) for a in V((n + 1) // 2) for b in V(n // 2)]
    evens = list(range(2, n + 1, 2))
    bad = 0
    for _ in range(T):
        bseq = rand_valid(2 * n) if mode == 'randB' else rand_slip(n, Vn)
        b2 = random.choice(pbs)
        sw = {}
        for i in evens:
            if random.random() < 0.5:
                sw[3 * i - 2], sw[3 * i - 1] = 3 * i - 1, 3 * i - 2
        seq = [sw.get(Bpan[b - 1], Bpan[b - 1]) for b in bseq] + \
              [sw.get(3 * (j - 1) + 2, 3 * (j - 1) + 2) for j in b2]
        bad += not valid_seq(seq, N)
    print(f"N={N} ({mode}): {T} tested, {bad} invalid")


def main():
    mode, n = sys.argv[1], int(sys.argv[2])
    if mode in ('randB', 'slipB'):
        return mainB(mode, n, int(sys.argv[3]))
    N = 3 * n
    Vn = V(n)
    pbs = [PB(a, b) for a in V((n + 1) // 2) for b in V(n // 2)]
    evens = list(range(2, n + 1, 2))
    bad = tot = 0
    if mode == 'exh':
        subsets = [s for r in range(len(evens) + 1) for s in combinations(evens, r)]
        for b1, b3, b2 in product(Vn, Vn, pbs):
            for DB in subsets:
                tot += 1
                bad += not valid_seq(build(b1, b3, b2, DB), N)
    else:
        random.seed(2)
        for _ in range(int(sys.argv[3])):
            b1, b3, b2 = random.choice(Vn), random.choice(Vn), random.choice(pbs)
            DB = [i for i in evens if random.random() < 0.5]
            tot += 1
            bad += not valid_seq(build(b1, b3, b2, DB), N)
    print(f"N={N}: {tot} tested, {bad} invalid")


if __name__ == "__main__":
    main()

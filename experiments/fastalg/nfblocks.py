"""Does the trace normal form keep the block coordinates of rust/src/layout.rs?
python3 nfblocks.py N j
Block of T: (|L|, |R|, c) with L = T cap [0, h), R = T cap [N-h, N), c = middle panel
(odd N).  Reports how many j-sets change block under NF, and how far elements move."""
import sys
from collections import Counter
from common import masks


def main():
    N = int(sys.argv[1])
    j = int(sys.argv[2])
    lm, rm = masks(N)
    pc = int.bit_count
    h = N // 2

    def shift_ok(t, p):
        t2 = t ^ (1 << p) ^ (1 << (p - 1))
        if pc(t & lm[p]) != pc(t2 & lm[p - 1]) or pc(t & rm[p]) != pc(t2 & rm[p - 1]):
            return False
        two = (1 << p) | (1 << (p - 1))
        x = t & ~(1 << p)
        while x:
            b = x & -x
            e = b.bit_length() - 1
            x ^= b
            a, c = lm[e] & two, rm[e] & two
            if (a and a != two) or (c and c != two):
                return False
        return True

    def nf(t):
        while True:
            for p in range(1, N):
                if t >> p & 1 and not t >> (p - 1) & 1 and shift_ok(t, p):
                    t ^= (1 << p) ^ (1 << (p - 1))
                    break
            else:
                return t

    lowmask = (1 << h) - 1
    highmask = ((1 << N) - 1) ^ ((1 << (N - h)) - 1)

    def block(t):
        return (pc(t & lowmask), pc(t & highmask), (t >> h & 1) if N % 2 else 0)

    changed = 0
    tot = 0
    disp = Counter()
    for s in range(1 << N):
        if pc(s) != j:
            continue
        tot += 1
        t = nf(s)
        if block(t) != block(s):
            changed += 1
        a = [p for p in range(N) if s >> p & 1]
        b = [p for p in range(N) if t >> p & 1]
        disp[max(x - y for x, y in zip(a, b))] += 1
    print('N=%d j=%d sets=%d block changed by NF: %d   max displacement histogram %s'
          % (N, j, tot, changed, sorted(disp.items())))


if __name__ == '__main__':
    main()

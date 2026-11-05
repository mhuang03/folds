"""rotshow.py k [nu]: list rotation-stable sequences of the k-strip (tau and its rotation by nu
both semi-symmetric), lexicographically first for each start, or all with 'all'."""
import sys
from rotstable import arms_k


def search(k, nu, start, find_all=False):
    A = {m: arms_k(k, m) for m in range(1, k + 1)}
    rot = {t: (t - 1 + nu) % k + 1 for t in range(1, k + 1)}
    out = []

    def rec(seq, S, Sr):
        if len(seq) == k:
            out.append(list(seq))
            return not find_all
        for t in range(1, k + 1):
            if t in S:
                continue
            L, R = A[t]
            if len(L & S) != len(R & S):
                continue
            L2, R2 = A[rot[t]]
            if len(L2 & Sr) != len(R2 & Sr):
                continue
            seq.append(t)
            if rec(seq, S | {t}, Sr | {rot[t]}):
                return True
            seq.pop()
        return False

    rec([start], frozenset({start}), frozenset({rot[start]}))
    return out


if __name__ == '__main__':
    k = int(sys.argv[1])
    nus = [int(sys.argv[2])] if len(sys.argv) > 2 and sys.argv[2] != 'all' else range(k)
    for nu in nus:
        for t in range(1, k + 1):
            r = search(k, nu, t, 'all' in sys.argv[3:])
            print(nu, t, len(r), r[:4])

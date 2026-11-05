"""rotstable.py k1 k2: rotation-stable sequences.  For the k-strip and nu in [0, k), which t can
start a sequence tau that is semi-symmetric both as it stands and after the cyclic rotation
t -> ((t - 1 + nu) mod k) + 1?  (PROOFS.txt 2: residue chains mod k in [N], N >= 2k,
N = nu mod k, correspond to such tau via the mirror; class s can come first iff
k + 1 - s can start a rotation-stable tau.)  Prints the impossible starts per nu."""
import sys
from functools import lru_cache


def arms_k(k, m):
    r = min(m - 1, k - m)
    return frozenset(range(m - r, m)), frozenset(range(m + 1, m + r + 1))


def run(k):
    A = {m: arms_k(k, m) for m in range(1, k + 1)}
    res = {}
    for nu in range(k):
        rot = {t: (t - 1 + nu) % k + 1 for t in range(1, k + 1)}

        @lru_cache(maxsize=None)
        def ok(S):
            if len(S) == k:
                return True
            Sr = frozenset(rot[x] for x in S)
            for t in range(1, k + 1):
                if t in S:
                    continue
                L, R = A[t]
                if len(L & S) != len(R & S):
                    continue
                L2, R2 = A[rot[t]]
                if len(L2 & Sr) != len(R2 & Sr):
                    continue
                if ok(S | {t}):
                    return True
            return False

        bad = [t for t in range(1, k + 1) if not ok(frozenset({t}))]
        res[nu] = bad
    return res


if __name__ == '__main__':
    for k in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        r = run(k)
        print(k, ' '.join(f'nu{nu}:{b}' for nu, b in r.items() if b))
        sys.stdout.flush()

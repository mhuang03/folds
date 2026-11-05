"""Ruler sequences.  I(k)[p] = floor(k/2^l) - (p/2^l - 1)/2 with l = v_2(p): the runs
[floor(k/2^(l+1))+1, floor(k/2^l)] are placed descending at the positions of valuation l.
Check: I(k) valid in the N-strip for k <= (N+1)/2; and test variants (run directions) for
the initial segments J(N, k) with k > (N+1)/2."""
import itertools
import sys
from lib import valid_seq


def v2(p):
    l = 0
    while p % 2 == 0:
        p //= 2
        l += 1
    return l


def ruler(k, dirs=None):
    """dirs[l] = True: run l descending (default), False: ascending."""
    seq = []
    for p in range(1, k + 1):
        l = v2(p)
        i = (p // (1 << l) + 1) // 2  # 1-based index within run l
        hi = k >> l
        lo = (k >> (l + 1)) + 1
        if dirs is None or dirs[l]:
            seq.append(hi - i + 1)
        else:
            seq.append(lo + i - 1)
    return seq


NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 24
for N in range(2, NMAX + 1):
    bad = [k for k in range(1, (N + 1) // 2 + 1) if not valid_seq(N, ruler(k))]
    assert not bad, (N, bad)
print('I(k) = ruler(k) valid for k <= (N+1)/2, N <=', NMAX)
for N in range(4, NMAX + 1):
    res = []
    for k in range((N + 1) // 2 + 1, N + 1):
        L = k.bit_length()
        ok = [d for d in itertools.product([True, False], repeat=L) if valid_seq(N, ruler(k, d))]
        res.append((k, len(ok)))
    print(N, res)

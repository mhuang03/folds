"""findseq.py N a b ...: a full semi-symmetric sequence starting with the given prefix,
found by DFS guided by the reachability bitset (lexicographically first)."""
import sys
from lib import valid_step, reachable


def complete(N, prefix, order=None):
    """Lexicographically first completion of prefix (None if dead)."""
    S = set(prefix)
    seq = list(prefix)
    full = set(range(1, N + 1))
    if not reachable(N, full - S):
        return None
    # build the rest backwards: the rest reversed is an ordering of full - S from scratch;
    # equivalently forward with the complement check: placing m is ok iff valid and
    # full - S - {m} reachable.
    while len(seq) < N:
        cands = sorted(full - S, key=order) if order else sorted(full - S)
        for m in cands:
            if valid_step(N, S, m) and reachable(N, full - S - {m}):
                seq.append(m)
                S.add(m)
                break
        else:
            return None
    return seq


if __name__ == '__main__':
    N = int(sys.argv[1])
    print(complete(N, [int(a) for a in sys.argv[2:]]))

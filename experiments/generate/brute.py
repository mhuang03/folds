"""Brute-force enumeration of valid (semi-symmetric / symmetric) fold sequences, small N.

valid_seqs(N, sym=False) -> list of tuples (DFS with step pruning).
"""
import functools


def step_ok(N, S, m, sym=False):
    r = min(m - 1, N - m)
    if sym:
        return all(((m - d) in S) == ((m + d) in S) for d in range(1, r + 1))
    return sum((m - d) in S for d in range(1, r + 1)) == sum((m + d) in S for d in range(1, r + 1))


def is_valid(seq, N=None, sym=False):
    N = len(seq) if N is None else N
    if sorted(seq) != list(range(1, N + 1)):
        return False
    S = set()
    for m in seq:
        if not step_ok(N, S, m, sym):
            return False
        S.add(m)
    return True


@functools.lru_cache(maxsize=None)
def valid_seqs(N, sym=False):
    out = []
    pre = []
    S = set()

    def dfs():
        if len(pre) == N:
            out.append(tuple(pre))
            return
        for m in range(1, N + 1):
            if m not in S and step_ok(N, S, m, sym):
                S.add(m); pre.append(m)
                dfs()
                pre.pop(); S.discard(m)
    dfs()
    return out


if __name__ == "__main__":
    for N in range(1, 11):
        print(N, len(valid_seqs(N)), len(valid_seqs(N, True)))

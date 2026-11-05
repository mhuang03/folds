"""db.py M1 M2: DB(M, w): is there a valid M-world sequence starting with w in which, for every
j with 2j <= M, panel 2j comes before panel j?  (By the shift lemma, [1, w+1] is then live in
the (M+1)-world.)  Prints the w (with 2w > M) for which DB fails."""
import sys
from functools import lru_cache


def run(M):
    def ok(S, m):
        r = min(m - 1, M - m)
        return sum(1 for d in range(1, r + 1) if (m - d) in S) == \
            sum(1 for d in range(1, r + 1) if (m + d) in S)

    @lru_cache(None)
    def go(S):
        if len(S) == M:
            return True
        for m in range(1, M + 1):
            if m in S or not ok(S, m):
                continue
            if 2 * m <= M and 2 * m not in S:
                continue
            if go(S | {m}):
                return True
        return False

    return [w for w in range(1, M + 1) if 2 * w > M and not go(frozenset([w]))]


for M in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    print(M, run(M))

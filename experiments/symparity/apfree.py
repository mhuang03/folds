"""Enumerate 3-AP-free permutations of [N] (= symmetric fold sequences, Folds.symmetric_iff_apFree)
and semi-symmetric fold sequences, for small N."""


def enum(N):
    out = []
    seq = []
    placed = set()

    def ok(m):
        # placing m now is bad iff some earlier x has partner 2m - x in range and still unplaced
        for x in seq:
            y = 2 * m - x
            if 1 <= y <= N and y not in placed:
                return False
        return True

    def rec():
        if len(seq) == N:
            out.append(tuple(seq))
            return
        for m in range(1, N + 1):
            if m not in placed and ok(m):
                placed.add(m); seq.append(m); rec(); seq.pop(); placed.remove(m)
    rec()
    return out


def enum_semi(N):
    out = []
    seq = []
    S = set()

    def ok(m):
        r = min(m - 1, N - m)
        return sum((m - d) in S for d in range(1, r + 1)) == sum((m + d) in S for d in range(1, r + 1))

    def rec():
        if len(seq) == N:
            out.append(tuple(seq))
            return
        for m in range(1, N + 1):
            if m not in S and ok(m):
                S.add(m); seq.append(m); rec(); seq.pop(); S.remove(m)
    rec()
    return out

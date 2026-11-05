"""half.py q: the HALF problem of PROOFS.txt (live3) 1.3 for odd q, M = q - 1.
A = (a_1, ..., a_k), k = M/2: a valid partial sequence from scratch in the M-strip containing
exactly one point of each mirror pair {z, q - z}, with z before (2z mod q) whenever both are in
A.  For each start z0 prints all the SETS A that occur (sorted) and whether each is a window
copy of the k-strip."""
import sys


def arms(k, m):
    r = min(m - 1, k - m)
    return range(m - r, m), range(m + 1, m + r + 1)


def vstep(k, S, m):
    L, R = arms(k, m)
    return sum(1 for x in L if x in S) == sum(1 for x in R if x in S)


def is_copy(M, A):
    """3.1 of live/PROOFS: [M] \\ A balanced around every point of A."""
    C = set(range(1, M + 1)) - set(A)
    return all(vstep(M, C, x) for x in A)


def run(q, want_all=True):
    M = q - 1
    k = M // 2
    res = {}

    def rec(seq, S, z0):
        if len(seq) == k:
            res.setdefault(z0, set()).add(tuple(sorted(seq)))
            return
        for z in range(1, M + 1):
            if z in S or (q - z) in S:
                continue
            if (2 * z) % q in S:      # 2z placed before z: forbidden
                continue
            if vstep(M, S, z):
                rec(seq + [z], S | {z}, z0)

    for z0 in range(1, M + 1):
        rec([z0], {z0}, z0)
    return res


if __name__ == '__main__':
    q = int(sys.argv[1])
    M = q - 1
    res = run(q)
    for z0 in range(1, M + 1):
        sets = sorted(res.get(z0, []))
        print(z0, z0 % 4, len(sets), [(A, is_copy(M, A)) for A in sets[:6]])

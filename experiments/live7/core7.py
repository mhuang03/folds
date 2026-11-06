"""core7.py N1 N2 [rules]: the hard core (live6/core.py) with the two-sided Beatty copies
TB(N, p; L) = {floor(i(N+2)/(p+1)) : i <= L} + {N + 1 - floor((j(N+2) - 1)/(p+1)) : j <= p - L}
(2p <= N, 0 <= L <= p) added as a rule 'tb'.  A pair (u, v) is in TB(N, p; L) for some L iff
u = floor(i(N+2)/(p+1)), N + 1 - v = floor((j(N+2) - 1)/(p+1)), i + j <= p (preimage (i, p + 1 - j)),
or u, v both in the left part, or both in the right part (then L = p resp. L = 0)."""
import sys
sys.path.insert(0, '../live6')
from ucov import dead, inward, copies


def tb_copies(N):
    """TB copies with L = p (left part only), L = 0, and the pairs across: returns list of
    (p, left, right) with left[i] = floor(i M/q), right[j] = floor((j M - 1)/q) for i, j <= p."""
    out = []
    M = N + 2
    for p in range(1, N // 2 + 1):
        q = p + 1
        left = [None] + [i * M // q for i in range(1, p + 1)]
        right = [None] + [(j * M - 1) // q for j in range(1, p + 1)]
        out.append((p, left, right))
    return out


def good_pairs(N, rules):
    good = set()

    def add(x, y):
        if x > y:
            x, y = y, x
        good.add((x, y))
        good.add((N + 1 - y, N + 1 - x))
    for p, phi in copies(N, rules):
        for a in range(1, p + 1):
            for b in range(a + 1, p + 1):
                if not dead(p, a, b):
                    add(phi[a], phi[b])
    if 'tb' in rules:
        for p, left, right in tb_copies(N):
            # across pairs: left i, right j, i + j <= p: preimage (i, p + 1 - j)
            for i in range(1, p + 1):
                for j in range(1, p + 1 - i):
                    if not dead(p, i, p + 1 - j):
                        add(left[i], N + 1 - right[j])
                if not dead(p, i, p):  # j = p - i... handled: i + j = p
                    pass
            for i in range(1, p + 1):
                j = p - i
                if j >= 1 and not dead(p, i, p + 1 - j):
                    add(left[i], N + 1 - right[j])
            # pairs inside the left part (L = p) and inside the right part (L = 0)
            for a in range(1, p + 1):
                for b in range(a + 1, p + 1):
                    if not dead(p, a, b):
                        add(left[a], left[b])
                        add(N + 1 - right[b], N + 1 - right[a])
    return good


def core(N, rules):
    good = good_pairs(N, rules)
    out = []
    for u in range(1, N + 1):
        for v in range(u + 1, N + 1):
            if u > N + 1 - v or dead(N, u, v) or inward(N, u, v) or (u, v) in good:
                continue
            if 'one' in rules and u == 1 and v == N and N % 2 == 1:
                continue
            out.append((u, v))
    return out


if __name__ == '__main__':
    rules = set(sys.argv[3].split(',')) if len(sys.argv) > 3 else \
        {'beatty', 'dbl', 'one', 'swap', 'chiY', 'tb'}
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        c = core(N, rules)
        print(N, len(c), c, flush=True)

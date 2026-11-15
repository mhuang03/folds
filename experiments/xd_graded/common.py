"""Common code for the graded-graph experiments.

Gamma_N: vertices = subsets S of [N] (bitmask, bit m-1 <-> panel m), rank |S|,
edges S -> S+{m} whenever the step (S, m) is semi-symmetric.
"""


def masks(N):
    L = [0] * (N + 1)
    R = [0] * (N + 1)
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        for d in range(1, r + 1):
            L[m] |= 1 << (m - d - 1)
            R[m] |= 1 << (m + d - 1)
    return L, R


def gtable(N):
    """g[S] for all S (list of python ints), and the popcount table."""
    L, R = masks(N)
    g = [0] * (1 << N)
    g[0] = 1
    pc = [bin(x).count("1") for x in range(1 << N)]
    for S in range(1, 1 << N):
        t = 0
        x = S
        while x:
            b = x & -x
            m = b.bit_length()
            T = S ^ b
            if pc[T & L[m]] == pc[T & R[m]]:
                t += g[T]
            x ^= b
        g[S] = t
    return g, pc


def vertex_sets(N, kind):
    """kind in {'all','reach','live'}; returns (levels, g, pc); levels[k] = sorted masks."""
    g, pc = gtable(N)
    full = (1 << N) - 1
    lev = [[] for _ in range(N + 1)]
    for S in range(1 << N):
        if (kind == 'all' or (kind == 'reach' and g[S])
                or (kind == 'live' and g[S] and g[full ^ S])):
            lev[pc[S]].append(S)
    return lev, g, pc


def up_edges(N, lev, pc):
    """E[k] = list of (i, j, m): lev[k][i] -> lev[k+1][j] is an edge adding panel m."""
    L, R = masks(N)
    E = []
    for k in range(N):
        idx = {S: j for j, S in enumerate(lev[k + 1])}
        e = []
        for i, S in enumerate(lev[k]):
            for m in range(1, N + 1):
                b = 1 << (m - 1)
                if S & b:
                    continue
                if pc[S & L[m]] == pc[S & R[m]]:
                    j = idx.get(S | b)
                    if j is not None:
                        e.append((i, j, m))
        E.append(e)
    return E


A = [None, 1, 2, 4, 10, 28, 96, 256, 1120, 4256, 17878, 70960, 383476, 1620328, 9167908,
     47821296, 276182312, 1481994716, 10084180418, 55082188120, 398874108930]

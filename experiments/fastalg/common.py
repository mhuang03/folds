"""Shared helpers for small N: validity, the g/f tables and the counting bisimulation."""


def masks(N):
    lm = [0] * N
    rm = [0] * N
    for p in range(N):
        r = min(p, N - 1 - p)
        for d in range(1, r + 1):
            lm[p] |= 1 << (p - d)
            rm[p] |= 1 << (p + d)
    return lm, rm


def tables(N):
    lm, rm = masks(N)
    pc = int.bit_count

    def valid(s, p):
        return pc(s & lm[p]) == pc(s & rm[p])

    M = 1 << N
    full = M - 1
    g = [0] * M
    g[0] = 1
    for s in range(1, M):
        a = 0
        t = s
        while t:
            b = t & -t
            p = b.bit_length() - 1
            t ^= b
            pre = s ^ b
            if g[pre] and valid(pre, p):
                a += g[pre]
        g[s] = a
    f = [0] * M
    f[full] = 1
    for s in range(full - 1, -1, -1):
        a = 0
        t = full & ~s
        while t:
            b = t & -t
            p = b.bit_length() - 1
            t ^= b
            if valid(s, p):
                a += f[s | b]
        f[s] = a
    return valid, g, f


def bisimF(N, valid, g, f):
    """Coarsest counting bisimulation of the backward DP on live sets (0 = not live)."""
    M = 1 << N
    cls = [0] * M
    for k in range(N, -1, -1):
        H = {}
        for s in range(M):
            if int.bit_count(s) != k or not (g[s] and f[s]):
                continue
            v = []
            for p in range(N):
                if not s >> p & 1 and valid(s, p) and cls[s | 1 << p]:
                    v.append(cls[s | 1 << p])
            key = tuple(sorted(v))
            if key not in H:
                H[key] = len(H) + 1
            cls[s] = H[key]
    return cls


def bits(s, N):
    return ''.join('x' if s >> i & 1 else '.' for i in range(N))

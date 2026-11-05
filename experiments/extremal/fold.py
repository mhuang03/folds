"""Small helpers: validity, statistics, enumeration of semi-symmetric fold sequences."""


def reach(N, m):
    return min(m - 1, N - m)


def valid_step(N, S, m):
    r = reach(N, m)
    return sum((m - d) in S for d in range(1, r + 1)) == sum((m + d) in S for d in range(1, r + 1))


def free_step(N, S, m):
    r = reach(N, m)
    return not any((m - d) in S or (m + d) in S for d in range(1, r + 1))


def is_valid(N, a):
    if sorted(a) != list(range(1, N + 1)):
        return False
    S = set()
    for m in a:
        if not valid_step(N, S, m):
            return False
        S.add(m)
    return True


def nfree(N, a):
    S = set()
    c = 0
    for m in a:
        c += free_step(N, S, m)
        S.add(m)
    return c


def des(a):
    return sum(a[i] > a[i + 1] for i in range(len(a) - 1))


def lrmax(a):
    c = 0
    mx = 0
    for x in a:
        if x > mx:
            c += 1
            mx = x
    return c


def enum(N):
    out = []

    def rec(seq, S):
        if len(seq) == N:
            out.append(list(seq))
            return
        for m in range(1, N + 1):
            if m not in S and valid_step(N, S, m):
                seq.append(m)
                S.add(m)
                rec(seq, S)
                seq.pop()
                S.discard(m)

    rec([], set())
    return out


def lg(x):
    """floor(log2 x) for x >= 1, -1 for x = 0."""
    return x.bit_length() - 1


def F(N):
    """Conjectured max number of free steps: floor(log2(N+1)) + floor(log2((N+1)/3)) + 1."""
    return lg(N + 1) + lg((N + 1) // 3) + 1


def show(N, a):
    S = set()
    s = []
    for m in a:
        s.append(str(m) + ('*' if free_step(N, S, m) else ''))
        S.add(m)
    return ' '.join(s)

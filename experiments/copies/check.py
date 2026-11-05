"""Brute-force checks (N <= 12) of the paper statements formalised in Folds/Copies.lean."""
import itertools


def reach(N, m): return min(m - 1, N - m)


def valid(N, S, m):
    r = reach(N, m)
    return (sum(1 for d in range(1, r + 1) if m - d in S)
            == sum(1 for d in range(1, r + 1) if m + d in S))


def counts(N):
    """cnt[mask] = number of valid orderings of the set mask from scratch."""
    cnt = [0] * (1 << N)
    cnt[0] = 1
    for mask in range(1 << N):
        if not cnt[mask]:
            continue
        S = {i + 1 for i in range(N) if mask >> i & 1}
        for m in range(1, N + 1):
            if not mask >> (m - 1) & 1 and valid(N, S, m):
                cnt[mask | 1 << (m - 1)] += cnt[mask]
    return cnt


C = {N: counts(N) for N in range(0, 13)}
a = {N: C[N][(1 << N) - 1] for N in C}
print("a:", a)


def is_copy(N, X):
    X = sorted(X)
    p = len(X)
    for j in range(1, p + 1):
        for i in range(1, p + 1):
            if i == j:
                continue
            xj, xi = X[j - 1], X[i - 1]
            inL = xj - reach(N, xj) <= xi < xj
            iL = j - reach(p, j) <= i < j
            inR = xj < xi <= xj + reach(N, xj)
            iR = j < i <= j + reach(p, j)
            if inL != iL or inR != iR:
                return False
    return True


def bal(N, U, m):
    r = reach(N, m)
    return sum(1 for x in U if m - r <= x < m) == sum(1 for x in U if m < x <= m + r)


# 1. doubling splits
for j in range(1, 6):
    q = 2 * j + 1
    for n in range(1, 13):
        N = q * n
        A = [x for x in range(1, N + 1) if x % q in range(2, 2 * j + 1, 2)]
        B = [x for x in range(1, N + 1) if x not in A]
        assert len(A) == j * n and is_copy(N, A) and is_copy(N, B)
        for m in range(1, N + 1):
            assert bal(N, A, m) and bal(N, B, m)
        if N <= 12:
            assert a[N] >= 2 * a[j * n] * a[(j + 1) * n], (j, n)
print("1. doubling splits OK")

# 2. Beatty copies and the copy criterion
for N in range(1, 13):
    for p in range(1, N + 1):
        for g in range(2 * p - 1 - N, 1):
            X = [(r * N + g) // p for r in range(1, p + 1)]
            assert is_copy(N, X), (N, p, g)
    for mask in range(1, 1 << N):
        X = [i + 1 for i in range(N) if mask >> i & 1]
        crit = all(valid(N, set(X) - {x}, x) for x in X)
        assert crit == is_copy(N, X), (N, X)
print("2. Beatty copies, criterion OK")

# 3. shifted blocks
for n in range(2, 7):
    N = 2 * n
    j = n // 2
    X = [2 * y + (1 if y > j else 0) for y in range(1, n)]
    mask = sum(1 << (x - 1) for x in X)
    # sequences starting with the set X: (orderings of X) * (completions); a completion is
    # valid after X iff its reversal is valid from scratch.
    start = C[N][mask] * C[N][((1 << N) - 1) ^ mask]
    print(f"  n={n}: start-with-X {start}, a(n-1)a(n+1)={a[n-1]*a[n+1]}, a(2n)={a[N]},"
          f" 2a(n)^2={2*a[n]**2}")
    if n % 2 == 1 and n >= 3:
        assert start == a[n - 1] * a[n + 1] and a[N] >= 2 * a[n] ** 2 + a[n - 1] * a[n + 1]
    if n % 2 == 0 and n >= 4:
        assert 2 * start >= a[n - 1] * a[n + 1]
        assert 2 * a[N] >= 4 * a[n] ** 2 + a[n - 1] * a[n + 1]
print("3. shifted OK")

# 4. near-class copy, odd N
for N in range(3, 13, 2):
    X = [(r * N - 2) // ((N - 1) // 2) for r in range(1, (N - 1) // 2 + 1)]
    assert X == [1] + list(range(4, N, 2)), (N, X)
    assert is_copy(N, X)
    Y = [x for x in range(1, N + 1) if x not in X]
    assert C[N][sum(1 << (y - 1) for y in Y)] > 0
print("4. near-class OK")


# 5. one outside element: N = 2n+2, b = n+2, 2a-1 <= n+1, a >= 2
def Cm(N, perm, m):
    i = perm.index(m)
    return valid(N, set(perm[:i]), m)


for N in (4, 6, 8):
    n = (N - 2) // 2
    b = n + 2
    perms = list(itertools.permutations(range(1, N + 1)))
    for aa in range(2, (n + 2) // 2 + 1):
        ca = sum(Cm(N, p, aa) for p in perms)
        cb = sum(Cm(N, p, b) for p in perms)
        cab = sum(Cm(N, p, aa) and Cm(N, p, b) for p in perms)
        print(f"  N={N} a={aa} b={b}: {cab * len(perms)} vs {ca * cb}")
        assert cab * len(perms) == ca * cb
print("5. independence OK")

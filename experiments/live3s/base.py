# common helpers: strip [N], reach, arm counts, valid steps, Theorem G
def reach(N, m): return min(m - 1, N - m)
def L(N, S, m):
    r = reach(N, m); return sum(1 for x in S if m - r <= x < m)
def R(N, S, m):
    r = reach(N, m); return sum(1 for x in S if m < x <= m + r)
def valid(N, S, m): return m not in S and 1 <= m <= N and L(N, S, m) == R(N, S, m)
def valid3(N, a, b, c):
    for (x, y, z) in [(a,b,c),(a,c,b),(b,a,c),(b,c,a),(c,a,b),(c,b,a)]:
        if valid(N, {x}, y) and valid(N, {x, y}, z): return True
    return False
def dead3(N, a, b, c):
    if a == 1 and b % 2 == 0 and c == b + 1 and 4 <= b and 2 * b <= N + 3: return True
    if c == N and b == a + 1 and (N - a) % 2 == 0 and 4 <= N - a and 2 * (N - a) <= N + 3: return True
    if N % 2 == 1 and N >= 7 and ((a == 1 and b == 2 and c in (N - 1, N)) or (b == N - 1 and c == N and a in (1, 2))): return True
    return False
def inward1(N, S):
    # Theorem G with centre 1/2: every outside panel has R <= L
    return all(R(N, S, m) <= L(N, S, m) for m in range(1, N + 1) if m not in S)
def centre(N, S):
    neg = [m for m in range(1, N + 1) if m not in S and L(N, S, m) < R(N, S, m)]
    pos = [m for m in range(1, N + 1) if m not in S and L(N, S, m) > R(N, S, m)]
    return (not neg or not pos or max(neg) < min(pos))
def cs12(N):
    return [c for c in range(3, N + 1) if valid3(N, 1, 2, c) and not dead3(N, 1, 2, c)]

# the closed-form families OneTwo of Folds/Live3s.lean
def onetwo(N, c):
    return ((N % 4 == 1 and N >= 17 and c % 2 == 1 and 7 <= c and c + 4 <= N) or
            (N % 2 == 0 and N >= 16 and c % 2 == 1 and 7 <= c < N and (N % 4 == 0 or c + 5 <= N)) or
            (N % 2 == 0 and N >= 16 and c % 2 == 0 and 8 <= c and c + 2 <= N and (N % 4 == 0 or c + 6 <= N)) or
            (N % 4 == 3 and N >= 19 and c % 2 == 0 and 8 <= c and c + 5 <= N) or
            (N % 4 == 3 and c % 4 == 1 and 13 <= c and c + 6 <= N))

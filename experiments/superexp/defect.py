"""Induced window system of a set X subset [N] on its index set, compared with the |X|-strip.
Used to understand the 'slip' defects (odds with 2k+1 replaced by 2k)."""
import sys

def arms(N, m):
    r = min(m - 1, N - m)
    return set(range(m - r, m)), set(range(m + 1, m + r + 1))

def rel(N, x, y):  # where is y relative to the window of x
    L, R = arms(N, x)
    return 'L' if y in L else 'R' if y in R else '.'

def induced(N, X, bg=()):
    X = sorted(X)
    n = len(X)
    diffs = []
    for j in range(n):
        for i in range(n):
            if i == j:
                continue
            a = rel(N, X[j], X[i]); b = rel(n, j + 1, i + 1)
            if a != b:
                diffs.append((j + 1, i + 1, a, b))
    offs = []
    for j in range(n):
        L, R = arms(N, X[j])
        o = len(L & set(bg)) - len(R & set(bg))
        if o:
            offs.append((j + 1, o))
    return diffs, offs

if __name__ == '__main__':
    N = int(sys.argv[1])
    for k in range(1, N // 2):
        odds = set(range(1, N + 1, 2)); evens = set(range(2, N + 1, 2))
        X = (odds - {2 * k + 1}) | {2 * k}
        Y = (evens - {2 * k}) | {2 * k + 1}
        if len(X) != len(Y) and N % 2 == 0:
            continue
        dX, _ = induced(N, X)
        dY, oY = induced(N, Y, X)
        print(f"k={k}: X slip {2*k+1}->{2*k}: X diffs (j,i,actual,strip) {dX}")
        print(f"      Y diffs {dY}  Y offsets {oY}")

"""oneN.py N1 N2: explicit orderings for {1, N}, N odd (N != 7), by the recursion
   N = 1 (mod 4): {1, N} <- {1, (N+1)/2} through the odd class;
   N = 3 (mod 4): {1, N} <- {1, (N-1)/2} through the copy X_N = {1, 4, 6, ..., N-3, N},
                  X_N co-reachable via the odd strip n = (N+1)/2 and F = {2,4,..,n-4, n-1};
base: N <= 5, N = 9, 11, 13, 15 by exhaustive search.  Every ordering is checked."""
import sys
from lib import imb, solve


def theoremG(N, B):
    """Theorem G: background greedy (closest valid panel to a centre), reversed:
    a from-scratch ordering of [N] minus B, or None."""
    B = set(B)
    neg = [m for m in range(1, N + 1) if m not in B and imb(N, B, m) < 0]
    pos = [m for m in range(1, N + 1) if m not in B and imb(N, B, m) > 0]
    if neg and pos and max(neg) >= min(pos):
        return None
    c2 = 2 * max(neg) + 1 if neg else (2 * min(pos) - 1 if pos else 1)
    S = set(B)
    order = []
    U = set(range(1, N + 1)) - B
    while U:
        val = [m for m in U if imb(N, S, m) == 0]
        x = min(val, key=lambda m: abs(2 * m - c2))
        order.append(x)
        S.add(x)
        U.discard(x)
    return order[::-1]


def valid_scratch(N, seq, absent=()):
    S = set()
    for m in seq:
        if imb(N, S, m) != 0:
            return False
        S.add(m)
    return True


def coreach_X(N):
    """From-scratch ordering of [N] minus X_N (N = 3 mod 4, N >= 11)."""
    n = (N + 1) // 2
    F = set(range(2, n - 3, 2)) | {n - 1}
    Fc = set(range(1, n + 1)) - F
    tau = theoremG(n, F)          # orders Fc from scratch
    phi = theoremG(n, Fc)         # orders F from scratch
    sigma = phi + tau[::-1]       # full sequence, 2 before 1, n-1 before n
    assert valid_scratch(n, sigma) and len(sigma) == n
    assert sigma.index(2) < sigma.index(1) and sigma.index(n - 1) < sigma.index(n)
    mp = {1: 2, n: N - 1}
    bgorder = [mp.get(y, 2 * y - 1) for y in sigma]
    return bgorder[::-1]


def one_N(N):
    if N <= 15:
        o = solve(N, [1, N], list(range(2, N)))
        return o[::-1] if o else None
    if N % 4 == 1:
        p = (N + 1) // 2
        o = one_N(p)              # ordering of [2, p-1] in [p]
        # odd class: y -> 2y - 1; evens first (any full sequence of the even strip)
        e = (N - 1) // 2
        ev = full_seq(e)
        return [2 * y for y in ev] + [2 * y - 1 for y in o]
    p = (N - 1) // 2
    o = one_N(p)
    X = [1] + list(range(4, N - 2, 2)) + [N]
    psi = {i + 1: X[i] for i in range(p)}
    return coreach_X(N) + [psi[y] for y in o]


def full_seq(n):
    return theoremG(n, set()) if n > 0 else []


if __name__ == '__main__':
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1, 2):
        if N == 7:
            continue
        o = one_N(N)
        ok = o is not None and sorted(o) == list(range(2, N)) and valid_scratch(N, o)
        print(N, 'OK' if ok else 'FAIL', flush=True)
        if not ok:
            break

"""Parity balance by position: for each step k, #(valid sequences whose k-th panel is odd)
minus #(... even).  Brute-force DFS, symmetric and semi rules, small N."""
import sys


def valid(S, m, N, sym):
    r = min(m - 1, N - m)
    if sym:
        return all(((m - d) in S) == ((m + d) in S) for d in range(1, r + 1))
    return sum((m - d) in S for d in range(1, r + 1)) == sum((m + d) in S for d in range(1, r + 1))


def enum(N, sym):
    out = []
    seq = []
    S = set()

    def rec():
        if len(seq) == N:
            out.append(tuple(seq)); return
        for m in range(1, N + 1):
            if m not in S and valid(S, m, N, sym):
                S.add(m); seq.append(m); rec(); seq.pop(); S.remove(m)
    rec()
    return out


if __name__ == '__main__':
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    for sym in (True, False):
        print('symmetric' if sym else 'semi')
        for N in range(2, Nmax + 1):
            L = enum(N, sym)
            bal = [sum(1 if w[k] % 2 else -1 for w in L) for k in range(N)]
            # same for "panel k is placed at an odd step" (position parity of value k)
            print(f' N={N:2d} a={len(L):6d} (odd-even) by step:', bal)

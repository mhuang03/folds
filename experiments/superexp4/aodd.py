"""Aligned slips on ODD strips N = 2n+1.
X = {2i - e_i : i in [1,n]} (first block, order tau in V_n),
X^c = {2i - 1 + e_i : i in [1,n]} ∪ {2n+1} (second block, order sigma in V_{n+1}, index n+1 -> 2n+1).
For every E ⊆ [1,n]: is the set of good tau (resp. sigma) exactly the set satisfying the
pairwise order conditions common to all good ones?  Print the conditions.
Usage: python3 aodd.py n [maxE]
"""
import sys


def valid_seq(seq, N, S0=()):
    placed = [0] * (N + 2)
    for x in S0:
        placed[x] = 1
    for m in seq:
        r = min(m - 1, N - m)
        if sum(placed[m - d] for d in range(1, r + 1)) != sum(placed[m + d] for d in range(1, r + 1)):
            return False
        placed[m] = 1
    return True


def gen(n):
    out = []

    def rec(seq, used):
        if len(seq) == n:
            out.append(tuple(seq))
            return
        for m in range(1, n + 1):
            if not used[m]:
                r = min(m - 1, n - m)
                if sum(used[m - d] for d in range(1, r + 1)) == sum(used[m + d] for d in range(1, r + 1)):
                    used[m] = 1
                    seq.append(m)
                    rec(seq, used)
                    seq.pop()
                    used[m] = 0
    rec([], [0] * (n + 2))
    return out


def common(good, size):
    C = []
    for x in range(1, size + 1):
        for y in range(1, size + 1):
            if x != y and all(t.index(x) < t.index(y) for t in good):
                C.append((x, y))
    return C


def sat(t, C):
    pos = {m: i for i, m in enumerate(t)}
    return all(pos[a] < pos[b] for a, b in C)


def reduce_(C):
    """transitive reduction"""
    S = set(C)
    return sorted((a, b) for a, b in S if not any((a, c) in S and (c, b) in S for c in {y for _, y in S}))


def main(n, maxE):
    N = 2 * n + 1
    Vn, Vn1 = gen(n), gen(n + 1)
    nonchar = 0
    for bits in range(1 << n):
        E = {i + 1 for i in range(n) if bits >> i & 1}
        if len(E) > maxE:
            continue
        f = {i: 2 * i - (i in E) for i in range(1, n + 1)}
        s = {i: 2 * i - 1 + (i in E) for i in range(1, n + 1)}
        s[n + 1] = N
        X = list(f.values())
        gT = [t for t in Vn if valid_seq([f[x] for x in t], N)]
        gS = [t for t in Vn1 if valid_seq([s[x] for x in t], N, X)]
        CT, CS = common(gT, n), common(gS, n + 1)
        okT = gT and len(gT) == sum(sat(t, CT) for t in Vn)
        okS = gS and len(gS) == sum(sat(t, CS) for t in Vn1)
        if not (okT and okS):
            nonchar += 1
        print(f"E={sorted(E)} T {len(gT)}/{len(Vn)} {'char' if okT else 'NOT'} {reduce_(CT)} | "
              f"S {len(gS)}/{len(Vn1)} {'char' if okS else 'NOT'} {reduce_(CS)}")
    print("not characterised by pairs:", nonchar)


if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]) if len(sys.argv) > 2 else 99)

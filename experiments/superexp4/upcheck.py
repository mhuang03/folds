"""Upper odd slip positions of B(n), n = 2s+1 odd, with odds-first parity blocks.
k = 2i-1 with s+2 <= 2i, i <= s:
   PB(alpha, beta) places k before qq_n(k)        iff  alpha places i before qq_{s+1}(i)
   PB(alpha', beta') places pp_n(k) before k+1     iff  beta' places pp_s(i-1) before i
qq_n(j) = 2j mod* n, pp_n(k) = (2k+1) mod* n.  Exhaustive over all valid alpha, beta.
Also checks the lower range used by mSum (k <= s) is untouched (disjoint).
"""
from trunc import valid_seq


def V(n):
    out = []

    def rec(pre, S):
        if len(pre) == n:
            out.append(tuple(pre))
            return
        for m in range(1, n + 1):
            if m not in S:
                S.add(m)
                if valid_seq(pre + [m], n):
                    pre.append(m)
                    rec(pre, S)
                    pre.pop()
                S.discard(m)
    rec([], set())
    return out


def ms(x, n): return (x - 1) % n + 1


def PB(a, b): return tuple([2 * x - 1 for x in a] + [2 * y for y in b])


def before(t, x, y): return t.index(x) < t.index(y)


for s in range(2, 6):
    n = 2 * s + 1
    Va, Vb = V(s + 1), V(s)
    I = [i for i in range(1, s + 1) if 2 * i >= s + 2]
    bad = tot = 0
    for a in Va:
        for b in Vb:
            t = PB(a, b)
            for i in I:
                k = 2 * i - 1
                tot += 2
                bad += before(t, k, ms(2 * k, n)) != before(a, i, ms(2 * i, s + 1))
                bad += before(t, ms(2 * k + 1, n), k + 1) != before(b, ms(2 * i - 1, s), i)
    print(f"n={n}: |I|={len(I)} checks={tot} failures={bad}")

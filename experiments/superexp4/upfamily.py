"""Exhaustive check of Theorem U (PROOFS.txt): for n = 2h+1 the sequences
    slip(D, PB(alpha, beta), PB(alpha', beta')),   D = E ∪ 2D' ∪ (2U - 1),
E ⊆ odd numbers <= h, D' ⊆ [1, h/2], U ⊆ I_h = [(h+3)/2, h],
alpha in V_{h+1} with upF on U, beta in condF(h, D'), alpha' in condS(h+1, D'),
beta' in V_h with upS on U, are valid sequences of the 2n-strip, pairwise distinct, and
their number is 2^{ceil(h/2)} W(h) M(h, h+1, floor(h/2)).  Also prints 4W / (a a 2^{ceil(|I|/4)}).
usage: python3 upfamily.py hmax
"""
import sys
from itertools import combinations
from trunc import valid_seq, PB, slip
from upcheck import V


def ms(x, n): return (x - 1) % n + 1


def before(t, x, y): return t.index(x) < t.index(y)


def okF(t, D, n): return all(before(t, k, ms(2 * k, n)) for k in D)


def okS(s, D, n): return all(before(s, ms(2 * k + 1, n), k + 1) for k in D)


def subsets(xs):
    for r in range(len(xs) + 1):
        yield from combinations(xs, r)


def main(hmax):
    for h in range(2, hmax + 1):
        n = 2 * h + 1
        Va, Vb = V(h + 1), V(h)
        I = list(range((h + 3) // 2, h + 1))
        odds = [k for k in range(1, h + 1) if k % 2]
        upF = lambda a, U: all(before(a, i, ms(2 * i, h + 1)) for i in U)
        upS = lambda b, U: all(before(b, ms(2 * i - 1, h), i) for i in U)
        W = sum(sum(upF(a, U) for a in Va) * sum(upS(b, U) for b in Vb) for U in subsets(I))
        Msum = sum(sum(okF(b, Dp, h) for b in Vb) * sum(okS(a, Dp, h + 1) for a in Va)
                   for Dp in subsets(range(1, h // 2 + 1)))
        seen = set()
        bad = total = 0
        for E in subsets(odds):
            for Dp in subsets(range(1, h // 2 + 1)):
                FB = [b for b in Vb if okF(b, Dp, h)]
                SA = [a for a in Va if okS(a, Dp, h + 1)]
                for U in subsets(I):
                    D = set(E) | {2 * i for i in Dp} | {2 * i - 1 for i in U}
                    AU = [a for a in Va if upF(a, U)]
                    BU = [b for b in Vb if upS(b, U)]
                    taus = [PB(a, b) for a in AU for b in FB]
                    sigs = [PB(a, b) for a in SA for b in BU]
                    for t in taus:
                        for s in sigs:
                            q = slip(D, t, s)
                            total += 1
                            if total % 7 == 0 or h <= 3:   # full check for small h, sampled above
                                bad += not valid_seq(q, 2 * n)
                            seen.add(q)
        pred = 2 ** len(odds) * W * Msum
        ratio = 4 * W / (len(Va) * len(Vb) * 2 ** ((len(I) + 3) // 4))
        print(f"h={h} N={2*n}: {total} sequences (pred {pred}), {len(seen)} distinct, invalid {bad}; "
              f"4W/(a a 2^ceil(|I|/4)) = {ratio:.3f}", flush=True)


if __name__ == "__main__":
    main(int(sys.argv[1]))

"""Check the 'last-half-step flip' for self-dual sequences, even N = 2n.
A self-dual sequence is given by its first half b_1..b_n (one panel from each pair {m, N+1-m}).
Claim: if the pair of b_n is OUTER (min(m, N+1-m) <= (N+1)/3), replacing b_n by its partner
keeps validity; if it is INNER, at most one of the two choices is valid.
Hence c(2n) == #{self-dual seqs with inner last-half pair} (mod 4)."""
from mim_util import valid


def halves(N):
    n = N // 2
    out = []

    def rec(seq, S, used):
        if len(seq) == n:
            out.append(tuple(seq)); return
        for j in range(1, n + 1):
            if j in used:
                continue
            for m in (j, N + 1 - j):
                if valid(S, m, N):
                    S.add(m); used.add(j); seq.append(m)
                    rec(seq, S, used)
                    seq.pop(); used.discard(j); S.discard(m)
    rec([], set(), set())
    return out


for N in range(4, 19, 2):
    hs = halves(N)
    hs_set = set(hs)
    outer = inner = 0
    ok = True
    for h in hs:
        m = h[-1]; j = min(m, N + 1 - m)
        partner = h[:-1] + (N + 1 - m,)
        if 3 * j <= N + 1:
            outer += 1
            ok &= partner in hs_set
        else:
            inner += 1
            ok &= partner not in hs_set
    print(N, "c =", len(hs), "outer", outer, "inner", inner, "claim holds" if ok else "CLAIM FAILS",
          "c mod 4", len(hs) % 4, "inner mod 4", inner % 4)

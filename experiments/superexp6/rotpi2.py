"""Good class orders pi (pi and mu o pi valid in the d-strip, mu(s) = (rho+1-s) mod* d),
listed for small odd d with a classification (parity-block or not)."""
import sys
def valid_seq(seq, n):
    S = set()
    for m in seq:
        r = min(m - 1, n - m)
        if sum(1 for k in range(1, r + 1) if m - k in S) != sum(1 for k in range(1, r + 1) if m + k in S):
            return False
        S.add(m)
    return True
def allvalid(n):
    out = []
    def rec(seq, S):
        if len(seq) == n:
            out.append(tuple(seq)); return
        for m in range(1, n + 1):
            if m in S: continue
            r = min(m - 1, n - m)
            if sum(1 for k in range(1, r + 1) if m - k in S) == sum(1 for k in range(1, r + 1) if m + k in S):
                seq.append(m); S.add(m); rec(seq, S); seq.pop(); S.discard(m)
    rec([], set())
    return out
def ms(x, d):
    v = x % d
    return d if v == 0 else v
d = int(sys.argv[1])
V = allvalid(d)
for rho in range(d):
    good = [p for p in V if valid_seq([ms(rho + 1 - s, d) for s in p], d)]
    pb = [p for p in good if all(x % 2 == p[0] % 2 for x in p[:(d + 1) // 2 if p[0] % 2 else d // 2])]
    print("rho", rho, "good", len(good), "PB", len(pb), " ex:", good[:3], pb[:2])

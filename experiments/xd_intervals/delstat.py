"""Is any deletion map Valid(N) -> Valid(N-s) well defined?
For every valid N-sequence (time word t_1..t_N) delete a fixed set of panels, standardise,
and test validity in the (N-s)-strip.  Prints the fraction that stays valid, for
  ends (1,N), mid2 (two central panels), last2 (N-1,N), last (N), first-in-time, last-in-time
  (delete the panel placed first / last and close the gap), mid1 (floor(N/2)+1),
  and, for single deletions, the best panel position p (max over p of the valid fraction)."""
import sys

def masks(N):
    L = []; R = []
    for m in range(1, N + 1):
        r = min(m - 1, N - m); l = 0; rr = 0
        for d in range(1, r + 1):
            l |= 1 << (m - d - 1); rr |= 1 << (m + d - 1)
        L.append(l); R.append(rr)
    return L, R

def valid_seqs(N):
    L, R = masks(N); out = []
    seq = []
    def rec(S):
        if len(seq) == N:
            out.append(tuple(seq)); return
        for m in range(N):
            b = 1 << m
            if S & b: continue
            if bin(S & L[m]).count('1') == bin(S & R[m]).count('1'):
                seq.append(m + 1); rec(S | b); seq.pop()
    rec(0); return out

def is_valid(seq, N, LR):
    L, R = LR; S = 0
    for m in seq:
        if bin(S & L[m - 1]).count('1') != bin(S & R[m - 1]).count('1'): return False
        S |= 1 << (m - 1)
    return True

def delete(seq, dels):
    ds = sorted(dels)
    out = []
    for m in seq:
        if m in dels: continue
        out.append(m - sum(1 for d in ds if d < m))
    return tuple(out)

if __name__ == "__main__":
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    print("# N a(N) | fraction of valid N-sequences whose deletion is valid")
    print("# N a(N)  ends   mid2   last2  last   mid1   firstT lastT  best-single(p)  best-pair(p,q)")
    for N in range(3, NMAX + 1):
        V = valid_seqs(N); a = len(V)
        LR1 = masks(N - 1); LR2 = masks(N - 2)
        def frac(f, LR, k):
            return sum(1 for s in V if is_valid(f(s), N - k, LR)) / a
        res = []
        res.append(frac(lambda s: delete(s, {1, N}), LR2, 2))
        c = (N + 1) // 2
        res.append(frac(lambda s: delete(s, {c, c + 1}), LR2, 2))
        res.append(frac(lambda s: delete(s, {N - 1, N}), LR2, 2))
        res.append(frac(lambda s: delete(s, {N}), LR1, 1))
        res.append(frac(lambda s: delete(s, {N // 2 + 1}), LR1, 1))
        res.append(frac(lambda s: delete(s, {s[0]}), LR1, 1))
        res.append(frac(lambda s: delete(s, {s[-1]}), LR1, 1))
        best1 = max((frac(lambda s: delete(s, {p}), LR1, 1), p) for p in range(1, N + 1))
        best2 = max((frac(lambda s: delete(s, {p, q}), LR2, 2), p, q)
                    for p in range(1, N + 1) for q in range(p + 1, N + 1)) if N <= 10 else (float('nan'), 0, 0)
        print(N, a, " ".join("%.4f" % x for x in res), "%.4f(%d)" % best1, "%.4f(%d,%d)" % best2)
        sys.stdout.flush()

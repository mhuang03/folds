# transfer.py NMIN NMAX: how many of the valid, non-dead 3-sets that fail F3S (closed-form
# Theorem G) reduce to a smaller strip through a copy whose transfer is proven in Lean for
# arbitrary sets:
#   Z   centred Beatty copies Z(N,p) = {floor(k(N+2)/(p+1))}, 2p <= N  (Live7.coReach_z_transfer)
#   res residue classes s mod q, 2 <= q <= 12, with a residue chain (Live2.coReach_mod: all
#       classes except s = 1 for N = 1 mod q and s = q for N = -1 mod q; none for q = 2, 4, 8),
#       and the multiples of q when q | N + 1 (Adjacent.coReach_mult_transfer).
# The preimage (a 3-set of the smaller strip, not necessarily a valid prefix set) counts as
# co-reachable if it satisfies F3S or a completion is found by DFS (it is then co-reachable).
import sys
from functools import lru_cache
from inward3 import imb, Fsym
from endstep import valid_sets, dead

@lru_cache(maxsize=None)
def coreach(M, B):
    a, b, c = B
    if Fsym(M, a, b, c): return True
    full = (1 << M) - 1
    Lm = [0] * (M + 2); Rm = [0] * (M + 2)
    for m in range(1, M + 1):
        r = min(m - 1, M - m)
        for d in range(1, r + 1):
            Lm[m] |= 1 << (m - d - 1); Rm[m] |= 1 << (m + d - 1)
    bad = set(); cnt = [0]
    def dfs(S):
        if S == full: return True
        if S in bad or cnt[0] > 200000: return False
        cnt[0] += 1
        for m in range(1, M + 1):
            if S >> (m - 1) & 1: continue
            if bin(S & Lm[m]).count('1') == bin(S & Rm[m]).count('1') and dfs(S | 1 << (m - 1)):
                return True
        bad.add(S); return False
    return dfs((1 << (a - 1)) | (1 << (b - 1)) | (1 << (c - 1)))

def copies(N):
    """(name, list of elements x_1 < ... < x_p) of the transfer copies of the N-strip."""
    res = []
    for p in range(3, N // 2 + 1):
        res.append(('Z%d' % p, [k * (N + 2) // (p + 1) for k in range(1, p + 1)]))
    for q in range(2, 13):
        for s in range(1, q + 1):
            if s > N: continue
            if q not in (2, 4, 8) and ((s == 1 and N % q == 1) or (s == q and N % q == q - 1)):
                if not (s == q and (N + 1) % q == 0): continue
            res.append(('r%d/%d' % (s, q), list(range(s, N + 1, q))))
    return res

for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    hard = sorted(t for t in valid_sets(N) if not dead(N, *t) and not Fsym(N, *t)
                  and t[0] + t[2] <= N + 1)
    cps = copies(N)
    cov = 0; left = []
    for t in hard:
        ok = False
        for name, X in cps:
            if all(v in X for v in t) and len(X) >= 3:
                pre = tuple(X.index(v) + 1 for v in t)
                if coreach(len(X), pre):
                    ok = True; break
        if ok: cov += 1
        else: left.append(t)
    print(N, 'hard', len(hard), 'reduced', cov, 'left', len(left), left[:8])
    sys.stdout.flush()

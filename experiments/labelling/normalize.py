"""Normalisations of admissible labellings that keep admissibility and do not increase t.
lam-normal: c'(m) = max{c'(y)+1 : y > m, c(y) < c(m)} (0 if none)  (patience level of the
            right-heavy order sorted by (c, position));
rho-normal: the reverse-mirror analogue, c''(m) = T - 1 - max{...from the left}."""
from reduce_test import adm

def lam_normal(c):
    """c: list with c[0] unused, panels 1..N"""
    N = len(c) - 1; out = [None] * (N + 1)
    for m in range(N, 0, -1):
        out[m] = max([out[y] + 1 for y in range(m + 1, N + 1) if c[y] < c[m]], default=0)
    return out

def rho_normal(c):
    N = len(c) - 1; d = [None] * (N + 1)
    for m in range(1, N + 1):
        d[m] = max([d[x] + 1 for x in range(1, m) if c[x] > c[m]], default=0)
    T = max(d[1:]) + 1
    return [None] + [T - 1 - d[m] for m in range(1, N + 1)]

if __name__ == '__main__':
    import glob, sys
    for f in sys.argv[1:]:
        N, t = map(int, f.split('/')[-1][4:-4].split('_'))
        bad = 0; n = 0; fixed = set()
        for s in open(f):
            s = s.strip()
            if len(s) != N: continue
            c = [None] + [int(ch) for ch in s]
            for g in (lam_normal(c), rho_normal(c), rho_normal(lam_normal(c)), lam_normal(rho_normal(c))):
                if not adm([0] + g[1:]) or max(g[1:]) > max(c[1:]): bad += 1
            # iterate to a fixed point
            cur = c
            for _ in range(20):
                nxt = rho_normal(lam_normal(cur))
                if nxt == cur: break
                cur = nxt
            fixed.add(''.join(map(str, cur[1:])))
            n += 1
        print(N, t, n, 'bad', bad, 'fixed points', len(fixed))

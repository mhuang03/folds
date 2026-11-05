"""Test candidate reductions c (N, t labels) -> c' (N', t-1 labels) on enumerated admissible
labellings (files all_N_t.txt, one labelling per line, digits = labels of panels 1..N)."""
import sys, glob

def adm(c):
    """c: list indexed 1..N (c[0] unused)"""
    N = len(c) - 1
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        l = sum(1 for x in range(m - r, m) if c[x] <= c[m])
        rr = sum(1 for x in range(m + 1, m + r + 1) if c[x] < c[m])
        if l > rr:
            return False
    return True

def red_min(c, t):
    N = len(c) - 1; Np = (N - 1) // 2
    return [0] + [min(c[2 * y], c[2 * y + 1]) for y in range(1, Np + 1)]

def red_odd(c, t):
    N = len(c) - 1; Np = (N - 1) // 2
    return [0] + [c[2 * y + 1] for y in range(1, Np + 1)]

def red_evenm1(c, t):
    N = len(c) - 1; Np = (N - 1) // 2
    return [0] + [max(c[2 * y] - 1, 0) for y in range(1, Np + 1)]

def red_maxm1(c, t):
    N = len(c) - 1; Np = (N - 1) // 2
    return [0] + [max(max(c[2 * y], c[2 * y + 1]) - 1, 0) for y in range(1, Np + 1)]

REDS = dict(min=red_min, odd=red_odd, evenm1=red_evenm1, maxm1=red_maxm1)

if __name__ == '__main__':
    for f in sorted(glob.glob('all_*_*.txt')):
        N, t = map(int, f[4:-4].split('_'))
        L = [l.strip() for l in open(f) if l.strip()]
        res = {}
        for name, R in REDS.items():
            bad = 0; badlab = 0; ex = None
            for s in L:
                c = [0] + [int(ch) for ch in s]
                cp = R(c, t)
                if max(cp[1:] or [0]) > t - 2: badlab += 1
                if not adm(cp):
                    bad += 1
                    if ex is None: ex = s
            res[name] = (bad, badlab, ex)
        print(N, t, len(L), res)

"""twoside.py N1 N2: two-sided class copies
    X = {d i - e : 1 <= i <= a}  +  {N + 1 - (d' i - e') : 1 <= i <= b}
(e, e' in {0, 1}).  For each wide mixed-parity pair (u, v) check whether some such X is a
window copy (I_X = 0 on X), inward, has min u, max v and |X| = a + b good for {1, p}
(p <= 3 or p odd != 7)."""
import sys


def reach(N, m):
    return min(m - 1, N - m)


def imb_all(N, X):
    ind = [0] * (N + 2)
    for x in X:
        ind[x] = 1
    pre = [0] * (N + 2)
    for m in range(1, N + 1):
        pre[m] = pre[m - 1] + ind[m]
    out = [0] * (N + 1)
    for m in range(1, N + 1):
        r = reach(N, m)
        out[m] = (pre[m - 1] - pre[m - r - 1]) - (pre[m + r] - pre[m])
    return ind, out


def is_inward_copy(N, X):
    ind, I = imb_all(N, X)
    maxneg, minpos = 0, N + 1
    for m in range(1, N + 1):
        if ind[m]:
            if I[m]:
                return False
        elif I[m] < 0:
            maxneg = m
        elif I[m] > 0 and minpos > m:
            minpos = m
    return maxneg < minpos


def good(p):
    return p <= 3 or (p % 2 == 1 and p != 7)


def twoside_copies(N, u, v):
    up = N + 1 - v
    res = []
    for d, e in ((u, 0), (u + 1, 1)):
        for dp, ep in ((up, 0), (up + 1, 1)):
            for a in range(1, N // d + 1):
                L = [d * i - e for i in range(1, a + 1)]
                if L[-1] > N:
                    break
                for b in range(1, N // dp + 1):
                    R = [N + 1 - (dp * i - ep) for i in range(1, b + 1)]
                    if R[-1] <= L[-1]:
                        break
                    X = L + R[::-1]
                    if is_inward_copy(N, X):
                        res.append((d, e, a, dp, ep, b, X))
    return res


if __name__ == '__main__':
    N1, N2 = int(sys.argv[1]), int(sys.argv[2])
    for N in range(N1, N2 + 1):
        miss = []
        tot = 0
        for u in range(1, N + 1):
            for v in range(u + 1, N + 1):
                up = N + 1 - v
                if u > up or (v - u) % 2 == 0 or v - u - 1 <= max(u, up):
                    continue
                if u == 1 and v == N:
                    continue
                tot += 1
                cs = twoside_copies(N, u, v)
                if not any(good(len(c[-1])) for c in cs):
                    miss.append((u, v, sorted(set(len(c[-1]) for c in cs))))
        print(N, tot, 'miss', len(miss), miss, flush=True)

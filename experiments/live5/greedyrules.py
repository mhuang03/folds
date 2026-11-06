"""greedyrules.py: simple greedy rules (background picture: repeatedly place the valid panel
with the smallest key) on {1, N}, N odd; reports for which N each rule succeeds."""
import sys


def run(N, D, key):
    S = set(D)
    I = {}
    for m in range(1, N + 1):
        if m in S:
            continue
        r = min(m - 1, N - m)
        I[m] = sum(1 for x in S if m - r <= x < m) - sum(1 for x in S if m < x <= m + r)
    order = []
    while I:
        cand = [m for m in I if I[m] == 0]
        if not cand:
            return order, I
        x = min(cand, key=key)
        del I[x]
        order.append(x)
        for m in I:
            r = min(m - 1, N - m)
            if m - r <= x < m:
                I[m] += 1
            elif m < x <= m + r:
                I[m] -= 1
    return order, None


rules = {
    'small': lambda N: (lambda x: x),
    'large': lambda N: (lambda x: -x),
    'mid': lambda N: (lambda x: (abs(2 * x - N - 1), x)),
    'out': lambda N: (lambda x: (-abs(2 * x - N - 1), x)),
}
if __name__ == '__main__':
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    for name, rk in rules.items():
        ok = [N for N in range(lo, hi + 1, 2) if run(N, {1, N}, rk(N))[1] is None]
        print(name, ok)

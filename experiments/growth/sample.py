"""Sample (approximately uniform) valid fold sequences by SMC with resampling, and print
the time function t(panel) of a few of them.  Exploration only.

usage: python3 sample.py N particles seed
"""
import random
import sys


def valid_moves(S, N):
    cum = [0] * (N + 1)
    for x in range(1, N + 1):
        cum[x] = cum[x - 1] + (1 if x in S else 0)
    out = []
    for m in range(1, N + 1):
        if m in S:
            continue
        r = min(m - 1, N - m)
        if cum[m - 1] - cum[m - 1 - r] == cum[m + r] - cum[m]:
            out.append(m)
    return out


def main():
    N, P, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    random.seed(seed)
    parts = [[] for _ in range(P)]
    for _ in range(N):
        vs = [valid_moves(set(p), N) for p in parts]
        w = [len(v) for v in vs]
        idx = random.choices(range(P), weights=w, k=P)
        parts = [parts[i] + [random.choice(vs[i])] for i in idx]
    for p in parts[:: max(1, P // 3)][:3]:
        t = [0] * (N + 1)
        for k, m in enumerate(p):
            t[m] = k + 1
        print("seq  :", " ".join(map(str, p)))
        print("time :", " ".join(map(str, t[1:])))


if __name__ == "__main__":
    main()

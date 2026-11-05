"""List valid sequences with at most `k` descents (DFS with pruning)."""
import sys


def valid(S, m, N):
    r = min(m - 1, N - m)
    return sum((m - d) in S for d in range(1, r + 1)) == sum((m + d) in S for d in range(1, r + 1))


def run(N, kmax):
    out = []

    def rec(seq, S, des):
        if len(seq) == N:
            out.append((des, tuple(seq)))
            return
        for m in range(1, N + 1):
            if m in S:
                continue
            nd = des + (1 if seq and seq[-1] > m else 0)
            if nd > kmax or not valid(S, m, N):
                continue
            S.add(m); seq.append(m)
            rec(seq, S, nd)
            seq.pop(); S.discard(m)
    rec([], set(), 0)
    return out


if __name__ == "__main__":
    for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
        res = run(N, 3 if N >= 15 else 2)
        dmin = min(d for d, _ in res)
        best = [s for d, s in res if d == dmin]
        print(N, "min des", dmin, "count", len(best))
        for s in best[:12]:
            # print as ascending runs
            runs, cur = [], [s[0]]
            for x in s[1:]:
                if x > cur[-1]:
                    cur.append(x)
                else:
                    runs.append(cur); cur = [x]
            runs.append(cur)
            print("   ", " | ".join(" ".join(map(str, r)) for r in runs))

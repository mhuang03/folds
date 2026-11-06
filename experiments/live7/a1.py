import sys
sys.path.insert(0, '../live6')
from ucov import dead, inward
from collections import Counter


def inX(N, p, h, x):
    if (p * (x + 1) + h - 1) % N <= p - 1:
        return (p * (x + 1) + h - 1) // N
    return 0


st = Counter()
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    for u in range(1, N // 3 + 1):
        for up in range(u, N):
            v = N + 1 - up
            if v <= u:
                break
            if inward(N, u, v) or dead(N, u, v):
                continue
            best = None
            for p in range((N + 1) // 2, 1, -1):
                for h in (0, 1):
                    if h + 2 * p > N + 1:
                        continue
                    a = inX(N, p, h, u); b = inX(N, p, h, v)
                    if a and b and not dead(p, a, b):
                        best = ('R', N - 2 * p, h, a, b); break
                    a = inX(N, p, h, N + 1 - v); b = inX(N, p, h, N + 1 - u)
                    if a and b and not dead(p, a, b):
                        best = ('L', N - 2 * p, h, a, b); break
                if best:
                    break
            if best is None:
                print(N, u, up, 'NONE')
            else:
                st[best[1]] += 1
print(sorted(st.items()))

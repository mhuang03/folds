"""symstates.py a r: reachable states on the background S_a (N = 6a + r), projected to
(pL, placed positions t of G_L (t = m - a - 1), pR, placed positions of G_R (t = N - a - m))."""
import sys
a = int(sys.argv[1]); r = int(sys.argv[2])
N = 6 * a + r
D = {a, N + 1 - a} | set(range(2 * a + 2, N - 2 * a))
free = [m for m in range(1, N + 1) if m not in D]
def reach(m): return min(m - 1, N - m)
start = frozenset(D); seen = {start}; stack = [start]
while stack:
    S = stack.pop()
    for m in free:
        if m in S: continue
        rr = reach(m)
        if sum(1 for x in S if m - rr <= x < m) == sum(1 for x in S if m < x <= m + rr):
            T = S | {m}
            if T not in seen: seen.add(T); stack.append(T)
summ = set()
for S in seen:
    pL = sum(1 for x in S if x < a); pR = sum(1 for x in S if x > N + 1 - a)
    gl = tuple(m - a - 1 for m in sorted(S) if a < m <= 2 * a + 1)
    gr = tuple(N - a - m for m in sorted(S, reverse=True) if N - 2 * a <= m < N + 1 - a)
    summ.add((pL, gl, pR, gr))
print(len(seen), "states", len(summ), "projected", "complete:", frozenset(range(1, N + 1)) in seen)
for x in sorted(summ): print(x)

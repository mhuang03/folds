"""Count DFS nodes of the simple prefix search (check a constraint only once its whole window is
known), to see whether a kernel-checked search is feasible.
usage: dfs_nodes.py N t [--left]"""
import sys
sys.setrecursionlimit(10000)
N, t = int(sys.argv[1]), int(sys.argv[2]); left = '--left' in sys.argv
def r(m): return min(m - 1, N - m)
# constraints completed at prefix length k: panels m with m + r(m) == k (and r >= 1)
done_at = {}
for m in range(1, N + 1):
    if r(m) == 0: continue
    if left and 2 * m > N + 1: continue
    done_at.setdefault(m + r(m), []).append(m)
nodes = 0; leaves = 0
def ok(c, m):
    v = c[m - 1]; R = r(m)
    return sum(c[x - 1] <= v for x in range(m - R, m)) <= sum(c[x - 1] < v for x in range(m + 1, m + R + 1))
def dfs(c):
    global nodes, leaves
    nodes += 1
    k = len(c)
    if k == N: leaves += 1; return
    for v in range(t):
        c.append(v)
        if all(ok(c, m) for m in done_at.get(k + 1, [])): dfs(c)
        c.pop()
dfs([])
print(f'N={N} t={t}{" left" if left else ""}: nodes={nodes} solutions={leaves}')

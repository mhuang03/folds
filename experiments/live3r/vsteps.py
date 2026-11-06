# vsteps.py N "background" "steps": check that each step is valid after the growing background
# and that the final background satisfies Theorem G (some centre).
import sys
N = int(sys.argv[1]); S = set(map(int, sys.argv[2].split())); steps = list(map(int, sys.argv[3].split()))
def reach(m): return min(m - 1, N - m)
def imb(S, m):
    r = reach(m); return sum(1 for x in S if m - r <= x < m) - sum(1 for x in S if m < x <= m + r)
for m in steps:
    assert m not in S and imb(S, m) == 0, ('invalid step', m)
    S.add(m)
neg = [m for m in range(1, N + 1) if m not in S and imb(S, m) < 0]
pos = [m for m in range(1, N + 1) if m not in S and imb(S, m) > 0]
print('valid steps; inward' if (not neg or not pos or max(neg) < min(pos)) else 'NOT inward', len(steps))

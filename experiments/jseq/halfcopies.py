#!/usr/bin/env python3
"""halfcopies.py NMAX: copies of size N/2 (N = 2n even) <-> subsets U of Z/n closed under
i -> 2i and under 2i+1 -> i, via X = {2i+1 : i in U} ∪ {2i+2 : i not in U} (0 <= i < n).
Counts the closed sets (ideals of the reachability preorder) and compares with `copies`."""
import sys, subprocess, os
HERE = os.path.dirname(os.path.abspath(__file__))
sys.setrecursionlimit(100000)

def closed_count(n):
    succ = [set() for _ in range(n)]
    for i in range(n):
        succ[i].add((2 * i) % n)
        succ[(2 * i + 1) % n].add(i)
    reach = []
    for v in range(n):  # forward reachability sets
        seen = {v}; st = [v]
        while st:
            u = st.pop()
            for w in succ[u]:
                if w not in seen: seen.add(w); st.append(w)
        reach.append(frozenset(seen))
    # components = classes of mutual reachability
    comp = {}
    reps = []
    for v in range(n):
        key = frozenset(u for u in reach[v] if v in reach[u])
        if key not in comp: comp[key] = len(reps); reps.append(v)
    C = len(reps)
    creach = [frozenset(comp[frozenset(u2 for u2 in reach[u] if u in reach[u2])] for u in reach[r]) for r in reps]
    memo = {}
    def count(avail):
        if not avail: return 1
        if avail in memo: return memo[avail]
        c = min(avail)
        a1 = avail - creach[c]                                  # c in U
        a2 = frozenset(d for d in avail if c not in creach[d])  # c not in U
        r = count(a1) + count(a2)
        memo[avail] = r
        return r
    return C, count(frozenset(range(C)))

def brute_half(n):
    """direct check of the bijection for small n: closed U -> copy X"""
    N = 2 * n; res = 0
    for m in range(1 << n):
        U = {i for i in range(n) if m >> i & 1}
        ok = all(((2 * i) % n in U) for i in U) and all(((2 * i + 1) % n) not in U or i in U for i in range(n))
        if ok: res += 1
    return res

if __name__ == '__main__':
    for n in range(1, int(sys.argv[1]) + 1):
        C, f = closed_count(n)
        N = 2 * n
        out = subprocess.run([os.path.join(HERE, 'copies'), str(N), 'c', str(n)],
                             capture_output=True, text=True).stdout.split()
        b = brute_half(n) if n <= 16 else None
        print(N, n, 'components', C, 'closed', f, 'copies', out[2], 'brute', b,
              'OK' if int(out[2]) == f else 'MISMATCH')

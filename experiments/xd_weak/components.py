"""components.py: the flip graph on valid fold sequences.

  python3 components.py [NMAX=10] [semi|sym]

Vertices: valid sequences of [N].  Edges: swap two adjacent entries when the result is again
valid.  This is the 1-skeleton of the convention-(c) complex K_N (the subcomplex of the
permutohedron induced on the valid permutations; its faces are the (c)-valid weak orders).
Prints #vertices, #edges (= W_c(N,N-1)), #connected components, the multiset of component
sizes, and chi(K_N) = sum_k (-1)^(N-k) W_c(N,k) for comparison (from W_*.txt when available).
"""
import sys
from collections import Counter

NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 10
KIND = sys.argv[2] if len(sys.argv) > 2 else 'semi'


def make_ok(N):
    L, R = {}, {}
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        L[m] = sum(1 << (m - d) for d in range(1, r + 1))
        R[m] = sum(1 << (m + d) for d in range(1, r + 1))
    if KIND == 'semi':
        def ok(S, m):
            return bin(S & L[m]).count('1') == bin(S & R[m]).count('1')
    else:
        def ok(S, m):
            r = min(m - 1, N - m)
            return all(((S >> (m - d)) & 1) == ((S >> (m + d)) & 1) for d in range(1, r + 1))
    return ok


def valid_seqs(N, ok):
    out = []
    seq = []

    def rec(S):
        if len(seq) == N:
            out.append(tuple(seq))
            return
        for m in range(1, N + 1):
            if not (S >> m) & 1 and ok(S, m):
                seq.append(m)
                rec(S | (1 << m))
                seq.pop()
    rec(0)
    return out


def main():
    for N in range(1, NMAX + 1):
        ok = make_ok(N)
        V = valid_seqs(N, ok)
        idx = {v: i for i, v in enumerate(V)}
        parent = list(range(len(V)))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x
        edges = 0
        for v in V:
            for i in range(N - 1):
                w = v[:i] + (v[i + 1], v[i]) + v[i + 2:]
                j = idx.get(w)
                if j is not None and v < w:
                    edges += 1
                    a, b = find(idx[v]), find(j)
                    if a != b:
                        parent[a] = b
        comp = Counter(find(i) for i in range(len(V)))
        sizes = Counter(comp.values())
        print('N=%2d %s  vertices=%d edges=%d components=%d  sizes(size:count)=%s' % (
            N, KIND, len(V), edges, len(comp), dict(sorted(sizes.items()))))
        sys.stdout.flush()


if __name__ == '__main__':
    main()

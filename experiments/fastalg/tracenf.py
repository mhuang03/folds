"""Greedy left-shift normal form for traces.  python3 tracenf.py N j
On ALL j-sets: apply trace-preserving left shifts T -> T - p + (p-1) until none applies,
once choosing the leftmost applicable p each time and once the rightmost.  Reports
  traces, shift components, #distinct normal forms (leftmost / rightmost strategy),
  whether g is constant on normal-form fibres (it must be: same trace), and
  whether the two strategies agree (a sign of confluence)."""
import sys
from common import tables, masks


def main():
    N = int(sys.argv[1])
    j = int(sys.argv[2])
    valid, g, f = tables(N)
    lm, rm = masks(N)
    pc = int.bit_count

    def trace(t):
        out = []
        x = t
        while x:
            b = x & -x
            p = b.bit_length() - 1
            x ^= b
            out.append((pc(t & lm[p]), pc(t & rm[p])))
        return tuple(out)

    def nf(s, leftmost):
        while True:
            ts = trace(s)
            rng = range(1, N) if leftmost else range(N - 1, 0, -1)
            for p in rng:
                if s >> p & 1 and not s >> (p - 1) & 1:
                    t = s ^ (1 << p) ^ (1 << (p - 1))
                    if trace(t) == ts:
                        s = t
                        break
            else:
                return s

    sets = [s for s in range(1 << N) if pc(s) == j]
    ntr = len({trace(s) for s in sets})
    A = {s: nf(s, True) for s in sets}
    B = {s: nf(s, False) for s in sets}
    nA = len(set(A.values()))
    nB = len(set(B.values()))
    agree = sum(A[s] == B[s] for s in sets)
    okg = all(g[s] == g[A[s]] for s in sets)
    print('N=%d j=%d sets=%d traces=%d NF(leftmost)=%d NF(rightmost)=%d agree=%d/%d g-constant=%s'
          % (N, j, len(sets), ntr, nA, nB, agree, len(sets), okg))


if __name__ == '__main__':
    main()

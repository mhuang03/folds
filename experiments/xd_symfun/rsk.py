"""Part 2: RSK shapes, Knuth classes, classical involutions, cycle types.

a-encoding only is needed for P/Q: P(t) = Q(a), Q(t) = P(a) since t = a^{-1}.
usage: python3 rsk.py [Nmax]   (default 11)
"""
import sys
from bisect import bisect_left
from collections import Counter, defaultdict
from math import factorial
from common import load, partitions


def rsk(w):
    P, Q = [], []
    for i, x in enumerate(w, 1):
        r = 0
        while True:
            if r == len(P):
                P.append([x]); Q.append([i]); break
            row = P[r]
            j = bisect_left(row, x)
            if j == len(row):
                row.append(x); Q[r].append(i); break
            row[j], x = x, row[j]
            r += 1
    return tuple(map(tuple, P)), tuple(map(tuple, Q))


def inverse_rsk(P, Q):
    P = [list(r) for r in P]
    Q = [list(r) for r in Q]
    n = sum(len(r) for r in P)
    w = [0] * n
    for i in range(n, 0, -1):
        r = next(k for k in range(len(Q)) if Q[k] and Q[k][-1] == i)
        Q[r].pop()
        x = P[r].pop()
        while r > 0:
            r -= 1
            row = P[r]
            j = bisect_left(row, x) - 1          # largest entry smaller than x
            row[j], x = x, row[j]
        w[i - 1] = x
        P = [r_ for r_ in P if r_]
        Q = [r_ for r_ in Q if r_]
    return tuple(w)


def hook_f(lam):
    n = sum(lam)
    conj = [sum(1 for p in lam if p > j) for j in range(lam[0])] if lam else []
    h = 1
    for i, p in enumerate(lam):
        for j in range(p):
            h *= (p - j - 1) + (conj[j] - i - 1) + 1
    return factorial(n) // h


def evac(T):
    """Schuetzenberger evacuation, via P(reverse-complement of the reading word)."""
    n = sum(len(r) for r in T)
    word = [x for r in reversed(T) for x in r]
    rc = [n + 1 - x for x in reversed(word)]
    return rsk(rc)[0]


def transpose(T):
    return tuple(tuple(T[i][j] for i in range(len(T)) if j < len(T[i])) for j in range(len(T[0])))


def cycle_type(w):
    n = len(w); seen = [False] * n; ct = []
    for i in range(n):
        if not seen[i]:
            l = 0; j = i
            while not seen[j]:
                seen[j] = True; j = w[j] - 1; l += 1
            ct.append(l)
    return tuple(sorted(ct, reverse=True))


def knuth_moves(w):
    """elementary Knuth neighbours of w (swap the outer pair of a triple when the middle...)."""
    out = []
    w = list(w)
    for i in range(len(w) - 2):
        a, b, c = w[i], w[i + 1], w[i + 2]
        # yzx <-> yxz  (x<y<z): swap last two when first is between them
        if min(b, c) < a < max(b, c):
            v = w[:]; v[i + 1], v[i + 2] = c, b; out.append(tuple(v))
        # xzy <-> zxy : swap first two when last is between them
        if min(a, b) < c < max(a, b):
            v = w[:]; v[i], v[i + 1] = b, a; out.append(tuple(v))
    return out


def foata_fund(w):
    """Foata's first fundamental transformation (cycles -> word): write cycles with largest
    element first, cycles ordered by increasing largest element, erase parentheses."""
    n = len(w); seen = [False] * n; cycles = []
    for i in range(n, 0, -1):
        if not seen[i - 1]:
            cyc = []; j = i
            while not seen[j - 1]:
                seen[j - 1] = True; cyc.append(j); j = w[j - 1]
            cycles.append(cyc)
    cycles.sort(key=lambda c: c[0])
    return tuple(x for c in cycles for x in c)


def foata_second(w):
    """Foata's second fundamental transformation (maj -> inv)."""
    out = []
    for x in w:
        if out:
            last = out[-1]
            if last > x:
                blocks, cur = [], []
                for y in out:
                    cur.append(y)
                    if y > x:
                        blocks.append(cur); cur = []
            else:
                blocks, cur = [], []
                for y in out:
                    cur.append(y)
                    if y < x:
                        blocks.append(cur); cur = []
            assert not cur
            out = [z for b in blocks for z in ([b[-1]] + b[:-1])]
        out.append(x)
    return tuple(out)


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    for N in range(1, nmax + 1):
        A = load(N)
        V = [tuple(int(x) for x in row) for row in A]
        VS = set(V)
        tot = len(V)
        shapes = Counter(); Pset = defaultdict(set); Qset = defaultdict(set)
        PQ = {}
        for w in V:
            P, Q = rsk(w)
            lam = tuple(len(r) for r in P)
            shapes[lam] += 1; Pset[lam].add(P); Qset[lam].add(Q)
            if N <= 9:
                PQ[w] = (P, Q)
        print(f"N={N} |V|={tot}")
        # shape distribution vs Plancherel
        nf = factorial(N)
        tv = 0.0; tr_ok = True; kn_ok = True; dk_ok = True
        rows = []
        for lam in partitions(N):
            f = hook_f(lam); c = shapes.get(lam, 0)
            tv += abs(c / tot - f * f / nf)
            conj = tuple(sum(1 for p in lam if p > j) for j in range(lam[0]))
            tr_ok &= (c == shapes.get(conj, 0))
            if c:
                kn_ok &= (c == len(Pset[lam]) * f)
                dk_ok &= (c == len(Qset[lam]) * f)
            rows.append((lam, c, f, len(Pset[lam]), len(Qset[lam])))
        print(f"  shapes occurring: {sum(1 for r in rows if r[1])}/{len(rows)}  "
              f"TV distance to Plancherel: {tv/2:.4f}  transpose-symmetric: {tr_ok}")
        print(f"  union of Knuth classes (a): {kn_ok}   union of dual Knuth classes (a) = Knuth classes of t: {dk_ok}")
        if N <= 8:
            for lam, c, f, np_, nq in rows:
                print(f"    {lam}: count {c}  f^lam {f}  (uniform-on-shape would be {tot*f*f/nf:.1f})  #P {np_}  #Q {nq}")
        else:
            lis = Counter()
            for lam, c, f, _, _ in rows:
                lis[lam[0]] += c
            print("    LIS distribution:", dict(sorted(lis.items())))
            print("    #P-tableaux/#SYT, #Q-tableaux/#SYT:",
                  sum(r[3] for r in rows), sum(r[4] for r in rows), sum(r[2] for r in rows))
        # direct Knuth closure
        closed = sum(1 for w in V if all(v in VS for v in knuth_moves(w)))
        inv = lambda w: tuple(sorted(range(1, N + 1), key=lambda m: w[m - 1]))
        Vinv = [inv(w) for w in V]
        closed_d = sum(1 for w in Vinv if all(inv(v) in VS for v in knuth_moves(w)))
        print(f"  sequences all of whose Knuth neighbours are valid: {closed}/{tot};  dual Knuth: {closed_d}/{tot}")
        # classical maps
        ninv = sum(1 for w in Vinv if w in VS)
        invol = sum(1 for w, wi in zip(V, Vinv) if w == wi)
        comp = sum(1 for w in V if tuple(N + 1 - x for x in w) in VS)
        rev = sum(1 for w in V if w[::-1] in VS)
        f1 = sum(1 for w in V if foata_fund(w) in VS)
        f2 = sum(1 for w in V if foata_second(w) in VS)
        print(f"  closed under: complement {comp == tot}, reversal {rev == tot};  "
              f"|V ∩ V^-1| = {ninv} (uniform expectation {tot*tot/nf:.1f});  involutions in V = {invol}")
        print(f"  Foata fundamental map: {f1} images valid;  Foata second map: {f2} images valid "
              f"(random expectation {tot*tot/nf:.1f})")
        if N <= 9:
            ev = sum(1 for w in V if inverse_rsk(PQ[w][0], evac(PQ[w][1])) in VS)
            ev2 = sum(1 for w in V if inverse_rsk(evac(PQ[w][0]), PQ[w][1]) in VS)
            tr = sum(1 for w in V if inverse_rsk(transpose(PQ[w][0]), transpose(PQ[w][1])) in VS)
            sw = sum(1 for w in V if inverse_rsk(PQ[w][0], PQ[w][0]) in VS)
            print(f"  (P,Q)->(P,evac Q): {ev} valid;  (evac P,Q): {ev2};  (P^T,Q^T): {tr};  (P,P): {sw}")
        # cycle types
        ct = Counter(cycle_type(w) for w in V)
        fix = Counter(sum(1 for i, x in enumerate(w, 1) if x == i) for w in V)
        cyc = Counter(len(cycle_type(w)) for w in V)
        print(f"  fixed points: {dict(sorted(fix.items()))}  mean {sum(k*v for k,v in fix.items())/tot:.4f}")
        print(f"  cycles: {dict(sorted(cyc.items()))}  mean {sum(k*v for k,v in cyc.items())/tot:.4f} "
              f"(H_N = {sum(1/k for k in range(1,N+1)):.4f})")
        ncyc = ct.get((N,), 0)
        print(f"  N-cycles: {ncyc} (uniform {tot/N:.1f});  distinct cycle types: {len(ct)}/{sum(1 for _ in partitions(N))}")
        if N <= 7:
            print("   ", dict(sorted(ct.items())))
        sys.stdout.flush()


if __name__ == '__main__':
    main()

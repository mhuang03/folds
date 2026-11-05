"""Exact recursions for the residue-class families R2 and R2c (see NOTES.txt, section 2).

R2  (compositions, q | N, outer order in R2(q); plus parity blocks):
    R2(1) = 1,  R2(N) = P(N) + sum_{q | N, 1 < q < N} P(q) R2(N/q)^q        (N >= 2)
    P(2) = 2,  P(q) = 0 for even q >= 4,  P(q) = 2 R2((q+1)/2) R2((q-1)/2) for odd q >= 3,
    and P(N) is used for N itself only when N = 2 or N is odd (parity blocks).
R2c (residue chains, any 2 <= q <= N/2 or q = 2, any valid class order, inner in R2c):
    R2c(N) = sum_q Prim(N, q) * prod_{s=1..q} R2c(n_s),   n_s = #{x <= N : x = s mod q}
    Prim(N, q) = number of class orders pi (ChainOK in the N-strip) that are not
    "coarsenable": for no divisor 1 < q' < q of q are the classes contiguous by residue
    mod q' with the q'-level order ChainOK.
usage: python3 r2c.py NMAX
"""
import sys
from math import prod
from functools import lru_cache


def arms(N):
    L, R = [0] * (N + 2), [0] * (N + 2)
    for m in range(1, N + 1):
        r = min(m - 1, N - m)
        for d in range(1, r + 1):
            L[m] |= 1 << (m - d - 1)
            R[m] |= 1 << (m + d - 1)
    return L, R


def pc(x):
    return bin(x).count("1")


def class_mask(N, q, s):
    m = 0
    x = s if s > 0 else q
    while x <= N:
        m |= 1 << (x - 1)
        x += q
    return m


def chain_orders(N, q):
    """All ChainOK orders of the q classes (lists of residues 1..q, q meaning 0)."""
    L, R = arms(N)
    cm = {s: class_mask(N, q, s % q) for s in range(1, q + 1)}
    elems = {s: [x for x in range(1, N + 1) if (cm[s] >> (x - 1)) & 1] for s in cm}
    out = []

    def bal(U, s):
        return all(pc(U & L[x]) == pc(U & R[x]) for x in elems[s])

    def rec(order, U, left):
        if not left:
            out.append(tuple(order))
            return
        for s in sorted(left):
            if bal(U, s):
                order.append(s)
                rec(order, U | cm[s], left - {s})
                order.pop()

    rec([], 0, frozenset(range(1, q + 1)))
    return out, cm, elems, L, R


def prim(N, q):
    orders, cm, elems, L, R = chain_orders(N, q)
    divs = [d for d in range(2, q) if q % d == 0]
    cnt = 0
    for pi in orders:
        coarse = False
        for d in divs:
            res = [s % d for s in pi]
            r = q // d
            blocks = [res[i * r:(i + 1) * r] for i in range(d)]
            if not all(len(set(b)) == 1 for b in blocks):
                continue
            # d-level ChainOK: union of complete d-classes balanced around next d-class
            U, ok = 0, True
            for b in range(d):
                cls = [pi[i] for i in range(b * r, (b + 1) * r)]
                for s in cls:
                    if not all(pc(U & L[x]) == pc(U & R[x]) for x in elems[s]):
                        ok = False
                if not ok:
                    break
                for s in cls:
                    U |= cm[s]
            if ok:
                coarse = True
                break
        if not coarse:
            cnt += 1
    return cnt, len(orders)


@lru_cache(None)
def R2(N):
    if N == 1:
        return 1

    def P(q):
        if q == 2:
            return 2
        if q % 2 == 0:
            return 0
        return 2 * R2((q + 1) // 2) * R2((q - 1) // 2)

    tot = P(N) if (N == 2 or N % 2 == 1) else 0
    for q in range(2, N):
        if N % q == 0:
            tot += P(q) * R2(N // q) ** q
    return tot


@lru_cache(None)
def R2c(N):
    if N == 1:
        return 1
    tot = 0
    qs = [2] + list(range(3, N // 2 + 1))
    for q in qs:
        p, _ = prim(N, q)
        sizes = [len(range(s, N + 1, q)) for s in range(1, q + 1)]
        tot += p * prod(R2c(n) for n in sizes)
    return tot


def prim_orders(N, q):
    """The non-coarsenable ChainOK orders themselves (see prim)."""
    orders, cm, elems, L, R = chain_orders(N, q)
    divs = [d for d in range(2, q) if q % d == 0]
    out = []
    for pi in orders:
        coarse = False
        for d in divs:
            res = [s % d for s in pi]
            r = q // d
            blocks = [res[i * r:(i + 1) * r] for i in range(d)]
            if not all(len(set(b)) == 1 for b in blocks):
                continue
            U, ok = 0, True
            for b in range(d):
                cls = [pi[i] for i in range(b * r, (b + 1) * r)]
                for s in cls:
                    if not all(pc(U & L[x]) == pc(U & R[x]) for x in elems[s]):
                        ok = False
                if not ok:
                    break
                for s in cls:
                    U |= cm[s]
            if ok:
                coarse = True
                break
        if not coarse:
            out.append(pi)
    return out, cm


def E_sets(N):
    """Non-parity neutral sets E_d, E_d^c (d | N odd, 3 <= d < N) as bitmasks."""
    full = (1 << N) - 1
    out = []
    for d in range(3, N, 2):
        if N % d == 0:
            E = sum(1 << (x - 1) for x in range(1, N + 1) if x % d and (x % d) % 2 == 0)
            out += [E, full ^ E]
    return out


@lru_cache(None)
def R3(N):
    """R3 = R2c ∪ neutral splits:  |A ∪ B| = |A| + |B| - |A ∩ B|,
    A = residue chains (minimal-q partition), B = disjoint union of the splits at E_d, E_d^c,
    A ∩ B counted through the minimal-q orders having an initial segment with union X."""
    if N == 1:
        return 1
    Es = E_sets(N)
    tot = 0
    for q in [2] + list(range(3, N // 2 + 1)):
        po, cm = prim_orders(N, q)
        sizes = [len(range(s, N + 1, q)) for s in range(1, q + 1)]
        w = prod(R3(n) for n in sizes)
        tot += len(po) * w
        for pi in po:
            U = 0
            for s in pi[:-1]:
                U |= cm[s]
                if U in Es:
                    tot -= w
    for X in Es:
        k = bin(X).count("1")
        tot += R3(k) * R3(N - k)
    return tot


if __name__ == "__main__":
    NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 15
    if len(sys.argv) > 2 and sys.argv[2] == "R3":
        for N in range(1, NMAX + 1):
            print(N, R3(N), flush=True)
        sys.exit()
    print("N R2 R2c  [q:Prim/#chains ...]")
    for N in range(1, NMAX + 1):
        info = []
        if N >= 2:
            for q in [2] + list(range(3, N // 2 + 1)):
                p, c = prim(N, q)
                info.append(f"{q}:{p}/{c}")
        print(N, R2(N), R2c(N), " ".join(info), flush=True)

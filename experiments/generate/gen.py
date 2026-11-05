#!/usr/bin/env python3
"""Generate (and verify) valid symmetric / semi-symmetric fold sequences of any length N.

Theory: experiments/generate/NOTES.txt.  Lean: Folds/Generate.lean.

Modes
-----
tree    (default) the recursive parity-block family, 2^(N-1) members.  Every member is
        symmetric (3-AP-free) and semi-symmetric.  Node (d, r) = residue class
        {x : x-1 = r mod 2^d}; its flip bit F(d, r) says which half goes first
        (0 = odd panels of the class, i.e. residue bit 0, first).  All flips 0 = the
        canonical sequence = bit-reversal order of [1..2^k] truncated to <= N.
        Choices: --seed S (pseudo-random flips) or --choices BITS (one bit per node of size
        >= 2, in order of (d, r); N-1 bits; missing bits are 0).
ladder  Montgomery ladder ("repeated squaring"): carries (R(m), R(m+1)) along the binary
        digits of N, one parity-block step per digit.  The flip depends only on the size
        of the block: a family of 2^(#sizes) <= 2^(2 log2 N) members (polynomial in N).
comp    iterated composition along a factorisation N = q1 q2 ... qt (--radix, default the
        prime factors in increasing order): residue classes mod q1 placed as blocks in the
        order of a valid q1-sequence, each class recursively.  Each node picks its block
        order from a pool of valid q-sequences (all of them for q <= 9, otherwise members of
        the tree family).  Semi-symmetric; symmetric only if every block order is.
slip    parity-slip recursion (superexp/PROOFS.txt Theorems 1-2): a node of size 2n
        exchanges 2k <-> 2k+1 between the parity classes for a seed-chosen set of odd k,
        its two blocks are odds-first parity blocks, whose halves recurse.  Family size
        2^slip_bits(N) = N^((1/8 + o(1)) N): super-exponential (e.g. 2^3145728 for N = 2^20,
        versus 2^(N-1) for tree).  Semi-symmetric, usually not symmetric.

Examples
--------
  python3 gen.py 8                      # 1 5 3 7 2 6 4 8
  python3 gen.py 10 --seed 7 --verify
  python3 gen.py 12 --choices 10110010001
  python3 gen.py 1000000 --seed 1 --verify --quiet
  python3 gen.py 1000000 --index 123456 # O(log N) random access (tree mode)
  python3 gen.py 360 --mode comp --radix 3,5,3,2,2,2 --seed 5 --verify
  python3 gen.py 1000000 --mode slip --seed 9 --verify --quiet
  python3 gen.py --selftest
"""
import argparse
import sys
import time

import numpy as np

MASK = (1 << 64) - 1


# ---------------------------------------------------------------- hashing
def _mix(z):
    """splitmix64 finaliser on a numpy uint64 array."""
    z = (z ^ (z >> np.uint64(30))) * np.uint64(0xBF58476D1CE4E5B9)
    z = (z ^ (z >> np.uint64(27))) * np.uint64(0x94D049BB133111EB)
    return z ^ (z >> np.uint64(31))


def hbits(seed, a, b):
    """pseudo-random 64-bit words for keys (seed, a, b); a, b arrays or ints."""
    with np.errstate(over="ignore"):
        s = np.uint64((seed * 0x9E3779B97F4A7C15) & MASK)
        z = _mix(np.asarray(a, dtype=np.uint64) * np.uint64(0xD6E8FEB86659FD93) + s)
        z = _mix(z ^ (np.asarray(b, dtype=np.uint64) + np.uint64(0x632BE59BD9B4E019)))
    return z


def nbits(N):
    return max(1, (N - 1).bit_length())


# ---------------------------------------------------------------- tree family
def node_offset(N, d):
    """index of node (d, 0) among the nodes of size >= 2, ordered by (d, r)."""
    return sum(min(1 << e, N - (1 << e)) for e in range(d) if (1 << e) < N)


def flips_tree(N, seed=None, choices=None):
    """returns F(d, r_array) -> 0/1 array."""
    if choices is not None:
        bits = np.array([c == "1" for c in choices] + [False], dtype=np.int64)

        def F(d, r):
            idx = node_offset(N, d) + r
            ok = (r + (1 << d) < N) & (idx < len(bits) - 1)
            return np.where(ok, bits[np.minimum(idx, len(bits) - 1)], 0)
        return F
    if seed is not None:
        return lambda d, r: (hbits(seed, d, r) & np.uint64(1)).astype(np.int64)
    return lambda d, r: np.zeros_like(r)


def gen_tree(N, F):
    """vectorised: sort panels by the key whose bit (K-1-d) is (residue bit d) xor F(d, r)."""
    if N <= 0:
        return np.zeros(0, dtype=np.int64)
    K = nbits(N)
    x0 = np.arange(N, dtype=np.int64)  # x - 1
    key = np.zeros(N, dtype=np.int64)
    for d in range(K):
        r = x0 & ((1 << d) - 1)
        b = (x0 >> d) & 1
        key |= (b ^ F(d, r)) << (K - 1 - d)
    return np.argsort(key, kind="stable") + 1


def tree_at(N, i, F):
    """i-th entry (0-based) of the tree-family sequence, O(log N) (Lean: genAt)."""
    assert 0 <= i < N
    d, r = 0, 0  # current node: x - 1 = r mod 2^d, size n
    n = N
    while n > 1:
        f = int(F(d, np.array([r]))[0])
        n_odd = (n + 1) // 2  # residue bit 0 child (x-1 = r mod 2^(d+1)) has ceil size
        n_even = n // 2
        first_bit, first_n = (0, n_odd) if f == 0 else (1, n_even)
        if i < first_n:
            bit, n = first_bit, first_n
        else:
            i -= first_n
            bit, n = 1 - first_bit, (n_even if f == 0 else n_odd)
        r |= bit << d
        d += 1
    return r + 1


def node_size(N, d, r):
    return (N - r + (1 << d) - 1) >> d


# ---------------------------------------------------------------- ladder
def scale(c, a):
    return 2 * a - c


def D(c_first, odd_seq, even_seq):
    """parity blocks: odds (2y-1) first if c_first == 1 else evens (2y) first."""
    if c_first == 1:
        return np.concatenate([scale(1, odd_seq), scale(0, even_seq)])
    return np.concatenate([scale(0, even_seq), scale(1, odd_seq)])


def gen_ladder(N, choose=lambda size: 1):
    """Montgomery ladder: (R(m), R(m+1)) -> (R(2m), R(2m+1)) or (R(2m+1), R(2m+2)).
    choose(size) = 1 for odds-first, 0 for evens-first.  O(log N) steps, O(N) work."""
    if N == 0:
        return np.zeros(0, dtype=np.int64)
    one = np.array([1], dtype=np.int64)
    A, B, m = one, np.array([1, 2], dtype=np.int64) if choose(2) == 1 else np.array([2, 1]), 1
    for bit in bin(N)[3:]:
        if bit == "0":   # (m, m+1) -> (2m, 2m+1)
            A, B = D(choose(2 * m), A, A), D(choose(2 * m + 1), B, A)
            m = 2 * m
        else:            # (m, m+1) -> (2m+1, 2m+2)
            A, B = D(choose(2 * m + 1), B, A), D(choose(2 * m + 2), B, B)
            m = 2 * m + 1
    return A


def ladder_choose(seed):
    if seed is None:
        return lambda size: 1
    return lambda size: 1 - int(hbits(seed, 1 << 40, size) & np.uint64(1))


# ---------------------------------------------------------------- composition
def prime_factors(n):
    out, p = [], 2
    while p * p <= n:
        while n % p == 0:
            out.append(p)
            n //= p
        p += 1
    if n > 1:
        out.append(n)
    return out


_POOL = {}


def pool(q, size=64):
    """list of valid q-sequences (as 0-based position tables)."""
    if q in _POOL:
        return _POOL[q]
    if q <= 9:
        from brute import valid_seqs
        seqs = [np.array(s) for s in valid_seqs(q)]
    else:
        seqs = [gen_tree(q, flips_tree(q, seed=s)) for s in range(size)]
    pos = np.zeros((len(seqs), q), dtype=np.int64)
    for k, s in enumerate(seqs):
        pos[k, s - 1] = np.arange(q)  # pos[k, digit] = place of class digit+1
    _POOL[q] = pos
    return pos


def gen_comp(N, radix=None, seed=None):
    """iterated residue-class composition along N = q1*q2*...*qt."""
    radix = radix or prime_factors(N)
    assert np.prod(radix, dtype=object) == N, "radix product must equal N"
    x0 = np.arange(N, dtype=np.int64)
    key = np.zeros(N, dtype=np.int64)
    Q = 1
    for d, q in enumerate(radix):
        r = x0 % Q
        digit = (x0 // Q) % q
        P = pool(q)
        if seed is None:
            sel = np.zeros(N, dtype=np.int64)
        else:
            sel = (hbits(seed, d + (1 << 41), r) % np.uint64(len(P))).astype(np.int64)
        key = key * q + P[sel, digit]
        Q *= q
    return np.argsort(key, kind="stable") + 1


# ---------------------------------------------------------------- slip recursion
def C_size(n):
    """|C_n| of the parity-slip recursion (superexp/PROOFS.txt Theorem 2)."""
    return n // 2 if n % 2 == 0 else (n + 1) // 4


_SB = {}


def slip_bits(n, forced=False):
    """log2 of the size of the slip family on a node of size n (exact: Theorem 1 says
    different choices give different sequences).  Returns (bits, use_slip)."""
    key = (n, forced)
    if key in _SB:
        return _SB[key]
    if n <= 1:
        res = (0, False)
    elif forced:
        res = (slip_bits((n + 1) // 2)[0] + slip_bits(n // 2)[0], False)
    else:
        par = 1 + slip_bits((n + 1) // 2)[0] + slip_bits(n // 2)[0]
        slp = -1
        if n % 2 == 0 and n >= 4:
            slp = C_size(n // 2) + 2 * slip_bits(n // 2, True)[0]
        res = (slp, True) if slp > par else (par, False)
    _SB[key] = res
    return res


def C_mask(n, i):
    """i in C_n (vectorised over i and n)."""
    odd = (i % 2) == 1
    return odd & (i >= 1) & np.where(n % 2 == 0, i <= n - 1, 2 * i + 1 <= n)


def gen_slip(N, seed=None):
    """Parity-slip recursion, vectorised level by level.  A node of size 2n (when the
    rule slip_bits says so) is split by Theorem 1 with a slip set D within C_n into the
    f-block (first) and the s-block, both ordered by ODDS-FIRST parity blocks (forced
    nodes), whose halves are again free nodes.  Other nodes: parity blocks with a free
    flip.  Family size 2^slip_bits(N) ~ N^(N/8) for N = 4^j."""
    s = 0 if seed is None else seed
    loc = np.arange(1, N + 1, dtype=np.int64)
    size = np.full(N, N, dtype=np.int64)
    nid = np.zeros(N, dtype=np.int64)
    forced = np.zeros(N, dtype=bool)
    key = np.zeros(N, dtype=np.int64)
    level = 0
    while (size > 1).any():
        done = size <= 1
        sizes = np.unique(size[~done])
        rule = {int(v): slip_bits(int(v))[1] for v in sizes}
        slip_size = np.isin(size, [v for v, u in rule.items() if u])
        slip = ~done & ~forced & slip_size
        par = ~done & ~slip
        bit = np.zeros(N, dtype=np.int64)
        nloc, nsize, nforced = loc.copy(), size.copy(), np.zeros(N, dtype=bool)
        # parity nodes
        if par.any():
            p = np.nonzero(par)[0]
            x, sz = loc[p], size[p]
            if seed is None:
                odd_first = np.ones(len(p), dtype=bool)
            else:
                odd_first = forced[p] | ((hbits(s, level, nid[p]) & np.uint64(1)) == 0)
            is_odd = (x % 2) == 1
            bit[p] = np.where(is_odd == odd_first, 0, 1)
            nloc[p] = np.where(is_odd, (x + 1) // 2, x // 2)
            nsize[p] = np.where(is_odd, (sz + 1) // 2, sz // 2)
        # slip nodes
        if slip.any():
            q = np.nonzero(slip)[0]
            x, n = loc[q], size[q] // 2
            i = x // 2
            if seed is None:
                di = np.zeros(len(q), dtype=bool)
            else:
                h = hbits(s, level + 1000, nid[q] * (1 << 21) + i)
                di = C_mask(n, i) & ((h & np.uint64(1)) == 1)
            inF = di == (x % 2 == 1)
            bit[q] = np.where(inF, 0, 1)
            nloc[q] = np.where(inF, i, i + 1)
            nsize[q] = n
            nforced[q] = True
        key = key * 2 + bit
        nid = nid * 2 + bit
        loc, size, forced = nloc, nsize, nforced
        level += 1
    return np.argsort(key, kind="stable") + 1


# ---------------------------------------------------------------- verification
def check_perm(seq, N):
    return len(seq) == N and np.array_equal(np.sort(seq), np.arange(1, N + 1))


def verify_semi(seq, N):
    """O(N log^2 N) numpy check of every semi-symmetric step (merge-sort tree)."""
    seq = np.asarray(seq, dtype=np.int64)
    if not check_perm(seq, N):
        return False
    if N <= 2:
        return True
    K = (N - 1).bit_length()
    size = 1 << K
    BIG = N + 2
    t = np.full(size, N + 1, dtype=np.int64)    # t[x-1] = time of panel x
    t[seq - 1] = np.arange(N)
    idx = np.arange(size, dtype=np.int64)
    levels = [np.sort((idx >> l) * BIG + t) for l in range(K + 1)]

    def C(h, T):  # #{x-1 < h : t < T}, vectorised over arrays h, T
        out = np.zeros_like(h)
        for l in range(K, -1, -1):
            has = (h >> l) & 1
            if not has.any():
                continue
            sel = np.nonzero(has)[0]
            hh = h[sel]
            base = (hh >> (l + 1)) << (l + 1)
            blk = base >> l
            out[sel] += np.searchsorted(levels[l], blk * BIG + T[sel]) - base
        return out

    m = np.arange(1, N + 1, dtype=np.int64)
    T = t[:N]
    r = np.minimum(m - 1, N - m)
    L = C(m - 1, T) - C(m - 1 - r, T)
    R = C(m + r, T) - C(m, T)
    return bool(np.all(L == R))


def verify_sym(seq, N):
    """O(N^2) check of the symmetric (3-AP-free) condition; for N <= ~30000."""
    seq = np.asarray(seq, dtype=np.int64)
    if not check_perm(seq, N):
        return False
    t = np.empty(N + 1, dtype=np.int64)
    t[seq] = np.arange(N)
    for m in range(2, N):
        r = min(m - 1, N - m)
        tm = t[m]
        left = t[m - r:m][::-1] < tm
        right = t[m + 1:m + r + 1] < tm
        if not np.array_equal(left, right):
            return False
    return True


# ---------------------------------------------------------------- self test
def bitrev_trunc(N):
    k = nbits(N)
    out = []
    for i in range(1 << k):
        v = int(format(i, "0%db" % k)[::-1], 2) + 1
        if v <= N:
            out.append(v)
    return np.array(out)


def selftest():
    from brute import is_valid, valid_seqs
    t0 = time.time()
    for N in range(1, 300):
        a = gen_tree(N, flips_tree(N))
        assert np.array_equal(a, bitrev_trunc(N)), N
        assert np.array_equal(a, gen_ladder(N)), N
        assert verify_semi(a, N) and verify_sym(a, N), N
    print("canonical = truncated bit reversal = ladder, valid: N < 300")
    for N in range(1, 120):
        for s in range(4):
            F = flips_tree(N, seed=s)
            a = gen_tree(N, F)
            assert verify_semi(a, N) and verify_sym(a, N), (N, s)
            M = N + 37
            b = gen_tree(M, flips_tree(M, seed=s))
            assert np.array_equal(b[b <= N], a), (N, s)   # truncation, whole family
            for i in range(0, N, max(1, N // 7)):
                assert tree_at(N, i, F) == a[i]
            ch = flips_tree(N, seed=s)
            sz = lambda size: 1 - int(hbits(s, 1 << 40, size) & np.uint64(1))
            Fl = lambda d, r: 1 - np.array([sz(int(node_size(N, d, int(v)))) for v in r])
            assert np.array_equal(gen_tree(N, Fl), gen_ladder(N, sz)), (N, s)
    print("random tree members valid; truncation of family; tree_at; ladder = size-flips")
    for N in range(1, 11):
        fam = set()
        nn = max(N - 1, 0)
        for mask in range(1 << nn):
            ch = format(mask, "0%db" % nn) if nn else ""
            fam.add(tuple(gen_tree(N, flips_tree(N, choices=ch)).tolist()))
        assert len(fam) == 2 ** nn, N
        assert fam <= set(valid_seqs(N, True)), N
    print("--choices enumerates exactly 2^(N-1) distinct symmetric sequences: N <= 10")
    for N in range(2, 200):
        for s in (None, 1, 2):
            a = gen_comp(N, seed=s)
            assert verify_semi(a, N), (N, s)
    for N in range(1, 9):
        a = valid_seqs(N)
        for s in a[:: max(1, len(a) // 20)]:
            assert verify_semi(np.array(s), N)
        bad = [s for s in __import__("itertools").permutations(range(1, N + 1))][:200]
        for s in bad:
            assert verify_semi(np.array(s), N) == is_valid(s, N), (N, s)
            assert verify_sym(np.array(s), N) == is_valid(s, N, True), (N, s)
    print("comp members valid N < 200; verifiers agree with brute force")
    for N in range(1, 300):
        for s in (None, 1, 2, 3):
            assert verify_semi(gen_slip(N, s), N), (N, s)
    print("slip members valid N < 300")
    print("selftest ok (%.1fs)" % (time.time() - t0))


# ---------------------------------------------------------------- CLI
def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("N", type=int, nargs="?")
    ap.add_argument("--mode", choices=["tree", "ladder", "comp", "slip"], default="tree")
    ap.add_argument("--seed", type=int)
    ap.add_argument("--choices", help="tree mode: bit string, one bit per node (N-1 bits)")
    ap.add_argument("--radix", help="comp mode: comma-separated factors of N")
    ap.add_argument("--index", type=int, help="tree mode: print only entry i (0-based), O(log N)")
    ap.add_argument("--verify", action="store_true", help="check semi-symmetry (and symmetry if N <= 20000)")
    ap.add_argument("--quiet", action="store_true", help="do not print the sequence")
    ap.add_argument("--out", help="write the sequence to this file")
    ap.add_argument("--selftest", action="store_true")
    a = ap.parse_args()
    if a.selftest:
        selftest()
        return
    if a.N is None:
        ap.error("N required")
    N = a.N
    if a.index is not None:
        print(tree_at(N, a.index, flips_tree(N, a.seed, a.choices)))
        return
    t0 = time.time()
    if a.mode == "tree":
        seq = gen_tree(N, flips_tree(N, a.seed, a.choices))
        fam = "2^%d" % max(N - 1, 0)
    elif a.mode == "ladder":
        seq = gen_ladder(N, ladder_choose(a.seed))
        fam = "ladder"
    elif a.mode == "slip":
        seq = gen_slip(N, a.seed)
        fam = "2^%d" % slip_bits(N)[0]
    else:
        radix = [int(v) for v in a.radix.split(",")] if a.radix else None
        seq = gen_comp(N, radix, a.seed)
        fam = "comp"
    t1 = time.time()
    text = " ".join(map(str, seq.tolist()))
    if a.out:
        with open(a.out, "w") as f:
            f.write(text + "\n")
    elif not a.quiet:
        print(text)
    print("# N=%d mode=%s family=%s generated in %.2fs" % (N, a.mode, fam, t1 - t0), file=sys.stderr)
    if a.verify:
        ok = verify_semi(seq, N)
        msg = "semi-symmetric: %s" % ok
        if N <= 20000:
            msg += ", symmetric: %s" % verify_sym(seq, N)
        print("# %s (%.2fs)" % (msg, time.time() - t1), file=sys.stderr)
        if not ok:
            sys.exit(1)


if __name__ == "__main__":
    main()

"""Family 7: mod structure.

 7a automaticity: for s = a mod m (m = 4, 8, 16, 3, 9; also (a/2) mod 2, (a/2) mod 4) and
    base k = 2 (m a power of 2, and all m), k = 3: the k-kernel elements s(k^e n + j) are
    compared on their common known range (>= 4 terms).  We report the number of DISTINCT
    kernel elements at depths e = 0, 1, 2 (k^e + ... elements), against the maximum, and
    against a random-sequence control with the same residue distribution.  A k-automatic
    sequence with a small automaton shows strong collapse; with 38 terms, depth 2 has only
    ~9 (k=2) / ~4 (k=3) known values per element, so this only detects SMALL automata.
 7b v_2(a(n)) and a(n) mod 8 as functions of the binary digits of n: number of conflicts
    for the hypotheses 'depends only on n mod 2^j' (j = 1..4), 'only on popcount(n)',
    'only on (popcount, n mod 4)', 'only on v_2(n)', 'only on (v_2(n), n mod 8)'.
 7c Gessel / Dwork-type congruences, p = 2, 3, 5, 7:  a(np) == a(n) (mod p, p^2),
    a(np^2) == a(np) (mod p^2), and also with c and J in place of a; observed vs chance.
 7d a - c mod 8, 16 (a == c mod 4 is proven): residue pattern by N mod 8."""
import random
from collections import Counter, defaultdict
from common2 import A, C, J, NMAX

random.seed(7)


def kernel_counts(s, k, maxdepth=2, minlen=4):
    """s: dict n -> value (n >= 1).  Distinct kernel elements per depth (prefix compare)."""
    out = []
    elems = []
    for e in range(maxdepth + 1):
        for j in range(k ** e):
            seq = []
            n = 1 if j == 0 else 0
            while k ** e * n + j <= NMAX:
                if k ** e * n + j >= 1:
                    seq.append(s[k ** e * n + j])
                n += 1
            if len(seq) >= minlen:
                elems.append((e, seq))
        # distinct among elements of depth <= e (compare on common prefix)
        reps = []
        for _, sq in elems:
            if not any(sq[:min(len(sq), len(r))] == r[:min(len(sq), len(r))] for r in reps):
                reps.append(sq)
        out.append((len(elems), len(reps)))
    return out


print('7a  k-kernel collapse  (elements, distinct) at depths 0..2; control = shuffled residues')
for name, m, f in (('a mod 4', 4, lambda n: A[n] % 4), ('a mod 8', 8, lambda n: A[n] % 8),
                   ('a mod 16', 16, lambda n: A[n] % 16), ('a/2 mod 2', 2, lambda n: (A[n] // 2) % 2),
                   ('a/2 mod 4', 4, lambda n: (A[n] // 2) % 4), ('a mod 3', 3, lambda n: A[n] % 3),
                   ('a mod 9', 9, lambda n: A[n] % 9), ('c mod 8', 8, lambda n: C[n] % 8)):
    s = {n: f(n) for n in range(1, NMAX + 1)}
    for k in (2, 3):
        res = kernel_counts(s, k)
        ctrl = []
        for t in range(20):
            vals = list(s.values())
            random.shuffle(vals)
            sc = {n: vals[n - 1] for n in range(1, NMAX + 1)}
            ctrl.append(kernel_counts(sc, k)[-1][1])
        print(f'   {name:10s} k={k}: {res}   control distinct at depth 2: mean {sum(ctrl)/len(ctrl):.1f} min {min(ctrl)}')
# control: Thue-Morse is 2-automatic with 2 kernel elements
tm = {n: bin(n).count('1') % 2 for n in range(1, NMAX + 1)}
print('   CONTROL Thue-Morse k=2:', kernel_counts(tm, 2))


def v2(x):
    k = 0
    while x % 2 == 0:
        x //= 2
        k += 1
    return k


print('\n7b  is v_2(a(n)) / a(n) mod 8 a function of these digit statistics?  (#conflicting classes / #classes with >= 2 members)')
hyps = {
    'n mod 2': lambda n: n % 2, 'n mod 4': lambda n: n % 4, 'n mod 8': lambda n: n % 8, 'n mod 16': lambda n: n % 16,
    'popcount(n)': lambda n: bin(n).count('1'), '(popcount, n mod 4)': lambda n: (bin(n).count('1'), n % 4),
    'v_2(n)': lambda n: v2(n), '(v_2(n), n mod 8)': lambda n: (v2(n), n % 8),
    '(popcount(n-1))': lambda n: bin(n - 1).count('1'), 'bitlength': lambda n: n.bit_length(),
}
print('   v_2(a(n)), n=2..38:', [v2(A[n]) for n in range(2, NMAX + 1)])
for tgt_name, tgt in (('v_2(a(n))', lambda n: v2(A[n])), ('a(n) mod 8', lambda n: A[n] % 8),
                      ('v_2(a(n)-c(n))', lambda n: v2(A[n] - C[n]) if A[n] != C[n] else 99)):
    line = []
    for hn, h in hyps.items():
        cls = defaultdict(set)
        cnt = Counter()
        for n in range(2, NMAX + 1):
            cls[h(n)].add(tgt(n))
            cnt[h(n)] += 1
        multi = [c for c in cls if cnt[c] >= 2]
        bad = [c for c in multi if len(cls[c]) > 1]
        line.append(f'{hn}: {len(bad)}/{len(multi)}')
    print(f'   {tgt_name:16s}', '; '.join(line))

print('\n7c  Gessel/Dwork-type congruences: successes / tests')
for sname, s, top in (('a', A, NMAX), ('c', C, 41), ('J', J, 33)):
    for p in (2, 3, 5, 7):
        for mod_e in (1, 2):
            pe = p ** mod_e
            ok = tot = 0
            for n in range(1, top // p + 1):
                tot += 1
                ok += (s[n * p] - s[n]) % pe == 0
            ok2 = tot2 = 0
            for n in range(1, top // (p * p) + 1):
                tot2 += 1
                ok2 += (s[n * p * p] - s[n * p]) % (p * p) == 0
            print(f'   {sname} p={p}: s(np)==s(n) mod p^{mod_e}: {ok}/{tot} (chance ~{tot/pe:.1f})'
                  + (f';  s(np^2)==s(np) mod p^2: {ok2}/{tot2}' if mod_e == 2 else ''))

print('\n7d  (a - c) mod 16 by N mod 8 (a == c mod 4 proven)')
for r in range(8):
    print(f'   N=={r} mod 8:', [(A[n] - C[n]) % 16 for n in range(1, NMAX + 1) if n % 8 == r])

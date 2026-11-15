"""Part 1: the quasisymmetric generating function Q_N = sum_{pi in V_N} F_{Des(pi)}.

Q is symmetric iff its coefficients in the monomial quasisymmetric basis,
    [M_beta] Q = #{pi in V_N : Des(pi) subset of S(beta)},
depend only on the partition obtained by sorting beta.  Same for the peak generating
function sum K_{Peak(pi)} (Stembridge): [M_beta] = 2^{l(beta)} #{pi : Peak(pi) subset S(beta) u (S(beta)+1)}.

usage: python3 qsym.py [Nmax]   (default 12)
"""
import sys
from collections import defaultdict
import numpy as np
from common import both, des_mask, peak_mask, comp_of_mask, subset_zeta, partitions


def analyse(N, enc, A, out):
    n = N - 1
    full = (1 << n) - 1
    c = np.bincount(des_mask(A), minlength=1 << n).astype(object)
    total = int(c.sum())
    # forced symmetries of the descent-set distribution
    comp_ok = all(c[D] == c[full ^ D] for D in range(1 << n))
    rev = lambda D: int(''.join(reversed(format(D, f'0{n}b'))), 2) if n else 0
    rev_ok = all(c[D] == c[rev(D)] for D in range(1 << n))
    m = subset_zeta(c, n)
    cls = defaultdict(list)
    for D in range(1 << n):
        comp = comp_of_mask(D, N)
        cls[tuple(sorted(comp, reverse=True))].append((comp, int(m[D])))
    bad = []
    l1 = 0
    msum = 0
    for lam, lst in cls.items():
        vals = [v for _, v in lst]
        mean = sum(vals) / len(vals)
        l1 += sum(abs(v - mean) for v in vals)
        msum += sum(vals)
        if min(vals) != max(vals):
            bad.append((lam, min(vals), max(vals), len(set(vals)), len(lst)))
    nparts = len(cls)
    out.write(f"N={N} enc={enc} Des: |V|={total} support={int((c>0).sum())}/{1<<n} "
              f"complement-invariant={comp_ok} reversal-invariant={rev_ok} "
              f"symmetric={not bad} violating-partitions={len(bad)}/{nparts} "
              f"L1-asymmetry={l1/msum:.4f}\n")
    if bad and N <= 6:
        for lam, lst in sorted(cls.items()):
            if len({v for _, v in lst}) > 1:
                out.write("    " + str(lam) + ": " + ", ".join(f"{cp}:{v}" for cp, v in lst) + "\n")
    elif bad:
        bad.sort(key=lambda b: (len(b[0]), b[0]))
        for lam, lo, hi, k, sz in bad[:4]:
            out.write(f"    e.g. {lam}: M-coefficients range {lo}..{hi} ({k} distinct values on {sz} compositions)\n")
    # peak function
    p = np.bincount(peak_mask(A), minlength=1 << n).astype(object)
    pz = subset_zeta(p, n)
    pcls = defaultdict(list)
    for D in range(1 << n):
        E = (D | (D << 1)) & full & ~1          # peaks live in positions 2..N-1
        comp = comp_of_mask(D, N)
        pcls[tuple(sorted(comp, reverse=True))].append((comp, int(pz[E | 0]) << len(comp)))
    # peak sets not contained in E: pz is a zeta transform over all masks, E as computed
    pbad = [lam for lam, lst in pcls.items() if len({v for _, v in lst}) > 1]
    out.write(f"N={N} enc={enc} Peak: distinct peak sets={int((p>0).sum())} "
              f"symmetric={not pbad} violating-partitions={len(pbad)}/{nparts}\n")
    if pbad and N <= 6:
        for lam in sorted(pbad):
            out.write("    " + str(lam) + ": " + ", ".join(f"{cp}:{v}" for cp, v in pcls[lam]) + "\n")
    return c


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    out = sys.stdout
    for N in range(1, nmax + 1):
        d = both(N)
        ca = analyse(N, 'a', d['a'], out)
        ct = analyse(N, 't', d['t'], out)
        same = all(ca[D] == ct[D] for D in range(len(ca)))
        out.write(f"N={N}: Des-set distribution of a equals that of t: {same}\n")
        out.flush()


if __name__ == '__main__':
    main()

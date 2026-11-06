"""Family 3b: standard OEIS-style transforms of a(N).

For each transform b we report: integrality, sign pattern, growth (log b(N)/b(N-1) at the
end), the unfactored part after removing primes < 10^4 (as a smoothness indicator), and
the outcome of the full P-recursive search of precursive.py (all (r,d) with K <= E-5).
'Simpler' would mean: much slower growth, smooth factorizations, or a recurrence.
"""
import math
from fractions import Fraction
from common import A, NMAX
import transforms as T
import precursive

SMALLP = [p for p in range(2, 10000) if all(p % q for q in range(2, int(p ** 0.5) + 1))]


def rough_digits(x):
    """digits of |x| after removing all prime factors < 10^4 (x integer)."""
    x = abs(int(x))
    if x == 0:
        return 0
    for p in SMALLP:
        while x % p == 0:
            x //= p
    return len(str(x)) if x > 1 else 0


def describe(name, b, out):
    L = len(b) - 1
    vals = [Fraction(b[n]) for n in range(1, L + 1)]
    integral = all(v.denominator == 1 for v in vals)
    signs = ''.join('+' if v > 0 else '-' if v < 0 else '0' for v in vals)
    tail = vals[-6:]
    grow = []
    for i in range(1, len(tail)):
        if tail[i - 1] != 0 and tail[i] != 0:
            grow.append(math.log(abs(tail[i] / tail[i - 1])))
    digits = [len(str(abs(v.numerator))) for v in vals[-3:]]
    rough = [rough_digits(v.numerator) for v in vals[-6:]] if integral else None
    with open('/dev/null', 'w') as dn:
        summ, found = precursive.run(name, b, dn)
    print(f"{name}", file=out)
    print(f"   integral={integral}  signs={signs}", file=out)
    print(f"   first terms: {[str(v) for v in vals[:10]]}", file=out)
    print(f"   numerator digits of last 3: {digits};  log-ratios at end: {[round(g, 2) for g in grow]}", file=out)
    if rough is not None:
        print(f"   digits of the part free of primes<1e4 (last 6 terms): {rough}", file=out)
    print(f"   P-rec search: {summ.split(None, 1)[1] if ' ' in summ else summ}", file=out)
    for f in found:
        print(f"   RELATION {f[:3]}", file=out)
    out.flush()


def main():
    import sys
    a = A
    TR = {
        'a itself': a,
        'Euler transform': T.euler(a),
        'inverse Euler transform': T.inv_euler(a),
        'Moebius transform': T.mobius_tr(a),
        'binomial transform (a0=1)': T.binomial(a, 1),
        'inverse binomial (a0=1)': T.inv_binomial(a, 1),
        'Stirling-2 transform': T.stirling2_tr(a),
        'Stirling-1 transform': T.stirling1_tr(a),
        'boustrophedon (a0=1)': T.boustrophedon(a, 1),
        'invert transform': T.invert(a),
        'inverse invert transform': T.inv_invert(a),
        'OGF log(1+A)': T.ogf_log(a),
        'EGF log(1+A) (connected)': T.egf_log(a),
        'a(N)/a(N-1) numerators? -> a(N) - N a(N-1)': [None] + [a[n] - n * a[n - 1] if n > 1 else a[1] for n in range(1, NMAX + 1)],
        'a(N)/2^(N-1) (vs recursive parity family)': [None] + [Fraction(a[n], 2 ** (n - 1)) for n in range(1, NMAX + 1)],
    }
    out = sys.stdout
    print(__doc__, file=out)
    for name, b in TR.items():
        describe(name, b, out)


if __name__ == '__main__':
    main()

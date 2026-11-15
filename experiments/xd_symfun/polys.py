"""Part 3: properties of the statistic polynomials (palindromic, unimodal, log-concave,
real-rooted, gamma-positive).  Reads data/dp_polys.txt (subset DP) and data/enum_polys.txt
(enumeration), cross-checks them on the overlap, prints a summary.
usage: python3 polys.py
"""
import os
from collections import defaultdict
import sympy as sp
from common import HERE, A_KNOWN

x = sp.symbols('x')


def read(fn):
    d = defaultdict(dict)
    with open(os.path.join(HERE, 'data', fn)) as f:
        for line in f:
            p = line.split()
            if len(p) < 3:
                continue
            d[p[1]][int(p[0])] = [int(v) for v in p[2:]]
    return d


def strip(c):
    c = list(c)
    while c and c[-1] == 0:
        c.pop()
    lo = 0
    while lo < len(c) and c[lo] == 0:
        lo += 1
    return lo, c[lo:]


def real_rooted(c):
    lo, c = strip(c)
    if len(c) <= 2:
        return True
    P = sp.Poly(list(reversed(c)), x)
    return sp.count_roots(P.sqf_part()) == P.sqf_part().degree()


def gamma(c):
    """gamma vector of a palindromic coefficient list (after stripping zeros), or None."""
    lo, c = strip(c)
    if c != c[::-1]:
        return None
    d = len(c) - 1
    c = c[:]
    g = []
    for j in range(d // 2 + 1):
        gj = c[j]
        g.append(gj)
        # subtract gj * x^j (1+x)^(d-2j)
        for i in range(d - 2 * j + 1):
            c[j + i] -= gj * sp.binomial(d - 2 * j, i)
    assert all(v == 0 for v in c)
    return [int(v) for v in g]


def props(c):
    lo, s = strip(c)
    pal = s == s[::-1]
    peak = s.index(max(s))
    uni = all(s[i] <= s[i + 1] for i in range(peak)) and all(s[i] >= s[i + 1] for i in range(peak, len(s) - 1))
    lc = all(s[i] * s[i] >= s[i - 1] * s[i + 1] for i in range(1, len(s) - 1))
    internal_zero = any(v == 0 for v in s)
    g = gamma(c) if pal else None
    return dict(lo=lo, deg=len(s) - 1, pal=pal, uni=uni, lc=lc and not internal_zero,
                gpos=(g is not None and all(v >= 0 for v in g)), gamma=g)


def main():
    dp = read('dp_polys.txt')
    en = read('enum_polys.txt')
    # cross-check
    alias = {'inv': 'a_inv', 'a_fix': 'a_fix'}
    bad = 0; checked = 0
    for name, rows in dp.items():
        ename = alias.get(name, name)
        for N, c in rows.items():
            assert sum(c) == (A_KNOWN[N - 1] if N <= len(A_KNOWN) else sum(c))
            if ename in en and N in en[ename]:
                a = strip(c); b = strip(en[ename][N])
                checked += 1
                if a != b:
                    bad += 1; print("MISMATCH", name, N)
    print(f"cross-check DP vs enumeration: {checked} polynomials compared, {bad} mismatches")
    allp = {}
    for name, rows in en.items():
        allp[name] = dict(rows)
    for name, rows in dp.items():
        allp.setdefault(alias.get(name, name), {}).update(rows)
    print("\nname: Nmax | palindromic | unimodal | log-concave | real-rooted | gamma-positive   (lists = N where it FAILS, N >= 4)")
    for name in sorted(allp):
        rows = allp[name]
        Ns = sorted(n for n in rows if n >= 4)
        f = defaultdict(list)
        for N in Ns:
            p = props(rows[N])
            for k in ('pal', 'uni', 'lc'):
                if not p[k]:
                    f[k].append(N)
            if p['pal'] and not p['gpos']:
                f['gpos'].append(N)
            if p['deg'] <= 60 and not real_rooted(rows[N]):
                f['rr'].append(N)
        def show(k):
            if k == 'gpos' and len(f['pal']) == len(Ns):
                return 'n/a'
            return 'all' if not f[k] else ('none' if len(f[k]) == len(Ns) else 'fails ' + ','.join(map(str, f[k])))
        print(f"{name}: {Ns[-1]} | {show('pal')} | {show('uni')} | {show('lc')} | {show('rr')} | {show('gpos')}")
    print("\ngamma vectors of the descent polynomials")
    for name in ('a_des', 't_des'):
        for N in sorted(allp[name]):
            if N >= 2:
                print(name, N, props(allp[name][N])['gamma'])
    print("\nselected polynomials")
    for name in ('t_des', 'a_exc', 't_pk', 'a_pk', 'a_lrmax', 'a_fix'):
        for N in sorted(allp[name]):
            lo, s = strip(allp[name][N])
            print(name, N, f"x^{lo} *", s)


if __name__ == '__main__':
    main()

#!/usr/bin/env python3
"""Factor the one-variable specialisations in polys.txt over Z[q]; evaluate at roots of unity."""
import sys, cmath
from sympy import symbols, Poly, factor_list, ZZ

q = symbols('q')
names = {0: 'sum D_m (shifted by sum r_m)', 1: 'sum |D_m|', 2: 'sum D_m^2', 3: '#{m: D_m != 0}'}
maxN_factor = int(sys.argv[1]) if len(sys.argv) > 1 else 14
for line in open('polys.txt'):
    head, coeffs = line.split(':')
    N, mode, deg = map(int, head.split())
    c = list(map(int, coeffs.split()))
    while c and c[-1] == 0: c.pop()
    lo = 0
    while c[lo] == 0: lo += 1
    print(f"N={N} mode={mode} [{names[mode]}] degree={len(c)-1} low={lo} f(1)={sum(c)} c0={c[0]}")
    if mode == 0:
        # value at q=-1 (signed count; exponent shift sum r_m has known parity)
        shift = sum(min(m - 1, N - m) for m in range(1, N + 1))
        sgn = sum(x * (-1) ** i for i, x in enumerate(c)) * (-1) ** shift
        vals = []
        for k in (3, 4, 5, 6):
            w = cmath.exp(2j * cmath.pi / k)
            v = sum(x * w ** (i - shift) for i, x in enumerate(c))
            vals.append(f"w{k}:{v.real:.6g}{v.imag:+.3g}i")
        print(f"   signed count sum_pi (-1)^(sum D) = {sgn};  central coeff (sum D = 0) = {c[shift]};  " + ' '.join(vals))
    if N <= maxN_factor:
        p = Poly(list(reversed(c)), q, domain=ZZ)
        cont, fl = factor_list(p)
        desc = ' * '.join(f"(deg {f.degree()}){'^'+str(e) if e > 1 else ''}" if f.degree() > 6 else f"({f.as_expr()}){'^'+str(e) if e > 1 else ''}" for f, e in fl)
        print(f"   content {cont}; factors: {desc}")

"""probe4.py F M0 M1: exact A_above, A_below at theta = 1/D with F free points; prints
A*D^F*48 etc. to look for the closed form (appends to w1D_F<F>.txt)."""
import sys
sys.path.insert(0, '../periods2')
from face import orbit, integrate

F, M0, M1 = map(int, sys.argv[1:4])
with open(f'w1D_F{F}.txt', 'a') as out:
    for M in range(M0, M1 + 1):
        D = 2 ** (M - 1) - 1
        v, bits = orbit(M, 1)
        Aa, Ab = integrate(v, bits, M + F)
        line = f'{M} {Aa} {Ab}'
        print(line, '   A_ab*D^F*', (Aa * D ** F).denominator, flush=True)
        out.write(line + '\n')
        out.flush()

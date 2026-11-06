import sys
sys.path.insert(0, '../periods2')
from face import orbit, integrate
from fractions import Fraction as Fr
for M in range(5, 15):
    D = 2**(M-1)-1
    v, bits = orbit(M, 1)
    Aa, Ab = integrate(v, bits, M+1)
    print(M, D, 'A_ab*D=', Aa*D, 'A_be*D=', Ab*D, flush=True)

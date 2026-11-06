"""probe5.py F M0 M1: chain weights A(W1 = 1 0^(n-1)), A(W2 = 1 1 0^(n-2)), A(W3 = 1^n) with F free
points; appends 'm A1 A2 A3' to chainW_F<F>.txt."""
import sys
from chainface import integrate

F, M0, M1 = map(int, sys.argv[1:4])
with open(f'chainW_F{F}.txt', 'a') as out:
    for M in range(M0, M1 + 1):
        n = M - 1
        W1 = (1,) + (0,) * (n - 1)
        W2 = (1, 1) + (0,) * (n - 2)
        W3 = (1,) * n
        A = [integrate(w, M + F) for w in (W1, W2, W3)]
        line = f'{M} ' + ' '.join(str(a) for a in A)
        print(line, [float(a) for a in A], flush=True)
        out.write(line + '\n')
        out.flush()

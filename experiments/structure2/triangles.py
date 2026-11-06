"""Item 1: refined triangles F(N,m) (= L(N,m) by reversal), F2(N,m1,m2), T(N,k),
reachable / alive counts.  Prints tables of ratios and simple identity tests.
usage: python3 triangles.py [semi|sym]"""
import sys, math
from fractions import Fraction as Fr
from common import counts, stats

rule = sys.argv[1] if len(sys.argv) > 1 else 'semi'
a, s = counts()
D = {}
for n in range(2, 31):
    try:
        D[n] = stats(n, rule)
    except StopIteration:
        pass
Ns = sorted(D)
A = {n: D[n]['total'] for n in Ns}
if rule == 'semi':
    assert all(A[n] == a[n] for n in Ns)
print(f'rule={rule}, N = {Ns[0]}..{Ns[-1]}')


def F(n, m):
    return D[n]['F'][m - 1]


def F2(n, m, x):
    return D[n]['F2'][m - 1][x - 1]


print('\n-- F(N,m)/a(N) for m = 1..4, the middle m = ceil(N/2), and N*F(N,1)/a(N) --')
for n in Ns:
    r = [F(n, m) / A[n] for m in range(1, min(n, 4) + 1)]
    mid = F(n, (n + 1) // 2) / A[n]
    print(f'{n:2d} ' + ' '.join(f'{x:.5f}' for x in r) + f'   mid {mid:.5f}  N*mid {n*mid:.4f}'
          f'  N*F1/a {n*F(n,1)/A[n]:.4f}  F1/F2 {F(n,1)/F(n,2):.4f}')

print('\n-- profile N*F(N,m)/a(N) against x = (m-1/2)/N (shape of the first-panel law) --')
for n in Ns[-4:]:
    print(n, ' '.join(f'{n*F(n,m)/A[n]:.3f}' for m in range(1, n + 1)))

print('\n-- F(N,1) against smaller a: F(N,1)/a(N-1), F(N,1)/(N a(N-1)/ ... ) --')
for n in Ns[2:]:
    print(n, F(n, 1), f'F1/a(N-1)={F(n,1)/A[n-1]:.4f}', f'F1/a(N)*N={n*F(n,1)/A[n]:.4f}',
          f'F(N,1)/F(N-1,1)={F(n,1)/F(n-1,1):.4f}', f'a(N)/a(N-1)={A[n]/A[n-1]:.4f}')

print('\n-- alternating / parity sums: E = sum over even m, O = sum over odd m --')
for n in Ns:
    E = sum(F(n, m) for m in range(2, n + 1, 2)); O = A[n] - E
    print(n, f'(O-E)/a={(O-E)/A[n]:+.5f}', 'O-E =', O - E)

print('\n-- second moment: Var(m)/N^2 of the first panel --')
for n in Ns:
    mu = (n + 1) / 2
    var = sum(F(n, m) * (m - mu) ** 2 for m in range(1, n + 1)) / A[n]
    print(n, f'{var/n**2:.5f}', f'(uniform 1/12 = {1/12:.5f})')

print('\n-- F2(N,1,x): which x follow panel 1 (x >= N/2+1), distribution --')
for n in Ns[-3:]:
    row = [F2(n, 1, x) for x in range(1, n + 1)]
    print(n, 'support', [x for x in range(1, n + 1) if row[x - 1]], )
    print('   ', ' '.join(f'{v/F(n,1):.4f}' for v in row if v))

print('\n-- F2 zero pattern: #(m,x) with F2 = 0 vs T(N,2)-#valid --')
for n in Ns:
    z = sum(1 for m in range(1, n + 1) for x in range(1, n + 1) if m != x and F2(n, m, x) == 0)
    print(n, 'zero ordered pairs', z, ' invalid 2-prefixes', n * (n - 1) - n * n // 2,
          ' dead valid 2-prefixes', z - (n * (n - 1) - n * n // 2))

print('\n-- T(N,k)/T(N,k-1) (mean branching) at k = 1..N, and last-step ratios --')
for n in Ns[-3:]:
    P = D[n]['prefixes']
    print(n, ' '.join(f'{P[k]/P[k-1]:.3f}' for k in range(1, n + 1)))
print('T(N,N-2)/a(N):', ' '.join(f'{n}:{D[n]["prefixes"][n-2]/A[n]:.4f}' for n in Ns))
print('T(N,N-3)/a(N):', ' '.join(f'{n}:{D[n]["prefixes"][n-3]/A[n]:.4f}' for n in Ns if n > 3))

print('\n-- reachable sets R(N,k), sum, and ratio to 2^N --')
for n in Ns:
    R = D[n]['reach']
    al = D[n].get('alive')
    print(n, sum(R), f'{sum(R)/2**n:.4f}', f'alive {sum(al)/2**n:.4f}' if al else '',
          'R(N,3)=', R[3] if n >= 3 else '')

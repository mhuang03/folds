"""Summarise out/levels.txt: unimodality, totals, sequences to compare with the OEIS."""
import sys
from fractions import Fraction

rows = {}
N = None
for line in open('out/levels.txt'):
    if line.startswith('N='):
        N = int(line.split()[0][2:])
        rows[N] = []
    elif line.strip()[0].isdigit():
        rows[N].append([int(x) for x in line.split()])
NS = sorted(rows)
COL = dict(k=0, all=1, reach=2, live=3, e_all=4, e_reach=5, e_live=6, dia=7, one=8, T=9, Q=10, A=11)


def col(N, name):
    return [r[COL[name]] for r in rows[N]]


print("== live rank sizes (first half), unimodality, symmetry")
for N in NS:
    live = col(N, 'live')
    uni = all(live[k] <= live[k + 1] for k in range(N // 2))
    sym = live == live[::-1]
    print(N, live[:N // 2 + 1], 'unimodal' if uni else 'NOT unimodal', 'sym' if sym else 'NOT sym')
print("== reachable rank sizes, unimodality")
for N in NS:
    reach = col(N, 'reach')
    peak = max(range(N + 1), key=lambda k: reach[k])
    uni = all(reach[k] <= reach[k + 1] for k in range(peak)) and all(
        reach[k] >= reach[k + 1] for k in range(peak, N))
    print(N, reach, 'peak', peak, 'unimodal' if uni else 'NOT unimodal')
print("== totals: N, #reach, #live, #edges(all), #edges(reach), #edges(live)")
for N in NS:
    print(N, sum(col(N, 'reach')), sum(col(N, 'live')), sum(col(N, 'e_all')),
          sum(col(N, 'e_reach')), sum(col(N, 'e_live')))
print("== live sizes at fixed rank k as a sequence in N")
for k in range(0, 7):
    print(k, [col(N, 'live')[k] for N in NS if N >= k])
print("== reachable sizes at fixed rank k as a sequence in N")
for k in range(0, 7):
    print(k, [col(N, 'reach')[k] for N in NS if N >= k])
print("== middle rank: N, live, reach, binomial, live/binomial")
for N in NS:
    k = N // 2
    print(N, col(N, 'live')[k], col(N, 'reach')[k], col(N, 'all')[k],
          float(Fraction(col(N, 'live')[k], col(N, 'all')[k])))
print("== Q(N,k) = sum_{|S|=k} g(S)^2")
for N in NS:
    print(N, col(N, 'Q'))
print("== Qmid(N) = Q(N, floor(N/2)),  ratio a(N)/Qmid for even N (cosine of g and g o complement)")
for N in NS:
    k = N // 2
    a = rows[N][0][COL['A']]
    q = col(N, 'Q')[k]
    q2 = col(N, 'Q')[N - k]
    print(N, q, a, float(Fraction(a * a, q * q2)) ** 0.5)
print("== Qtot(N) = sum over all S of g(S)^2 ; Ttot(N) = sum over all S of g(S)")
print([sum(col(N, 'Q')) for N in NS])
print([sum(col(N, 'T')) for N in NS])
print("== Q(N,N-1) = sum_m (number of valid sequences ending in m)^2")
print([col(N, 'Q')[N - 1] for N in NS])
print("== diamonds / one-way pairs: totals over all ranks, and at rank 0")
print('dia total', [sum(col(N, 'dia')) for N in NS])
print('one total', [sum(col(N, 'one')) for N in NS])
print('dia rank0', [col(N, 'dia')[0] for N in NS])
print('one rank0', [col(N, 'one')[0] for N in NS])
print("== check A = a(N) at every rank:",
      all(len(set(col(N, 'A'))) == 1 for N in NS))
print("== check e_live, e_all symmetric (self-duality):",
      all(col(N, 'e_live')[:N] == col(N, 'e_live')[:N][::-1]
          and col(N, 'e_all')[:N] == col(N, 'e_all')[:N][::-1] for N in NS))
print("== sum_{|S|=k} g(S) up(S) = T(N,k+1) is the recursion; T(N,k):")
for N in NS[:12]:
    print(N, col(N, 'T'))

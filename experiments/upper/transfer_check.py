"""transfer_check.py -- checks of the discrepancy-transfer lemmas (PROOFS.txt section 2).

I_S(m) = Pt(2m-1) - 2 P(m-1)  (cyclic defect; equals J_S(m) for free m), P(y) = |S ∩ [1,y]|,
Pt(y) = P(y mod N) + floor(y/N) |S|.   E(y) = P(y) - s y / N.
Lemma 2.1 (sup):  max_y |E(y)| <= max_m |I(m)| + 1   (in the integer form
                  |N P(y) - s y| <= N (B + 1)).
Lemma 2.2 (L2):   sqrt(sum_y E(y)^2) <= sqrt(sum_m I(m)^2) + 2 sqrt(N).
Exhaustive for N <= 14, random sets for larger N; prints the worst ratios seen.
"""
import itertools, math, random, sys


def fields(N, S):
    s = len(S)
    P = [0] * (N + 1)
    for y in range(1, N + 1):
        P[y] = P[y - 1] + (1 if y in S else 0)
    def Pt(y):
        return P[y % N] + (y // N) * s
    I = [Pt(2 * m - 1) - 2 * P[m - 1] for m in range(1, N + 1)]
    E = [P[y] - s * y / N for y in range(0, N)]
    return I, E


def check(N, S, worst):
    I, E = fields(N, S)
    B = max(abs(v) for v in I)
    D = max(abs(v) for v in E)
    worst['sup'] = max(worst['sup'], D - B)  # lemma: <= 1
    l2E = math.sqrt(sum(v * v for v in E)); l2I = math.sqrt(sum(v * v for v in I))
    worst['l2'] = max(worst['l2'], (l2E - l2I) / math.sqrt(N))  # lemma: <= 2


worst = {'sup': -1e9, 'l2': -1e9}
for N in range(1, 15):
    for mask in range(1 << N):
        S = {i + 1 for i in range(N) if mask >> i & 1}
        check(N, S, worst)
print("exhaustive N<=14: max (maxE - maxI) = %.4f (<= 1),  max (|E|_2 - |I|_2)/sqrt N = %.4f (<= 2)"
      % (worst['sup'], worst['l2']))
random.seed(1)
worst = {'sup': -1e9, 'l2': -1e9}
for _ in range(3000):
    N = random.randint(15, 300)
    p = random.random()
    S = {m for m in range(1, N + 1) if random.random() < p}
    check(N, S, worst)
print("random N<=300:    max (maxE - maxI) = %.4f,  max (|E|_2 - |I|_2)/sqrt N = %.4f" % (worst['sup'], worst['l2']))

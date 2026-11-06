"""pathstat.py PATHFILE N : statistics of a valid sequence (one panel per line).
Prints deficit L = sum ln((N-k)/V_k), L/N, the linear richness (1/N) sum V_k/(N-k), the
Jensen bound -ln(mean V/f) (<= L/N), and the run bound V <= R + |A| (PROOFS.txt 3)."""
import sys, math
f = sys.argv[1]; N = int(sys.argv[2]); seq = [int(l) for l in open(f)]
assert sorted(seq) == list(range(1, N + 1))
J = [0] * (N + 2); inS = [0] * (N + 2)
L = lin = Lrun = 0.0
def s(p): return inS[(p - 1) % N + 1]
for k, x in enumerate(seq):
    fr = N - k
    free = [m for m in range(1, N + 1) if not inS[m]]
    V = sum(1 for m in free if J[m] == 0)
    assert J[x] == 0, (k, x)
    R = sum(1 for m in free if s(m + 1)) if k > 0 else 1
    A = sum(1 for m in free if not s(m + 1) and not s(2 * m) and not s(2 * m + 1))
    assert V <= R + A
    L += math.log(fr / V); lin += V / fr; Lrun += math.log(fr / min(fr, R + A))
    inS[x] = 1
    for q in range(x // 2 + 1, x): J[q] += 1
    for q in range(x + 1, (N + x) // 2 + 1): J[q] -= 1
print("N=%d L=%.3f L/N=%.4f meanV/f=%.4f -ln(meanV/f)=%.4f runbound L/N>=%.4f" % (
    N, L, L / N, lin / N, -math.log(lin / N), Lrun / N))

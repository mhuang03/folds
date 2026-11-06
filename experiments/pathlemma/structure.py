"""structure.py PATHFILE N : structure of a (near-)minimising path.
 * restrictions to residue classes mod 2 (are they valid N/2-paths?  their deficits)
 * per-step (k, V, f) summary in 8 time segments: mean V/f, frac of free zeros that are in
   long zero blocks (consecutive), runs R, mean |J| over free panels, max |J|
 * the 2D point set (x_k/N, k/N): max anchored-box discrepancy."""
import sys, math
f = sys.argv[1]; N = int(sys.argv[2]); seq = [int(l) for l in open(f)]

def valid_steps(seq, n):
    J = [0] * (n + 2); inS = [0] * (n + 2); bad = 0; L = 0.0
    for k, x in enumerate(seq):
        free = [m for m in range(1, n + 1) if not inS[m]]
        V = sum(1 for m in free if J[m] == 0)
        if J[x] != 0: bad += 1
        else: L += math.log((n - k) / V)
        inS[x] = 1
        for q in range(x // 2 + 1, x): J[q] += 1
        for q in range(x + 1, (n + x) // 2 + 1): J[q] -= 1
    return bad, L

for r in (1, 0):
    sub = [(x + 1) // 2 if r else x // 2 for x in seq if x % 2 == r]
    bad, L = valid_steps(sub, N // 2)
    print("class %s mod 2 -> %d-strip: invalid steps %d of %d" % ("odd" if r else "even", N // 2, bad, len(sub)))

# 2D anchored discrepancy of the point set
pts = sorted((x, k) for k, x in enumerate(seq))
D = 0
t = {x: k for k, x in enumerate(seq)}
for y in range(N + 1):
    # points with position <= y, cumulative in time
    times = sorted(t[x] for x in range(1, y + 1))
    c = 0
    for k in range(N + 1):
        while c < len(times) and times[c] < k: c += 1
        D = max(D, abs(c - k * y / N))
print("max anchored discrepancy of the space-time point set: %.2f (ln N = %.2f)" % (D, math.log(N)))

J = [0] * (N + 2); inS = [0] * (N + 2); rows = []
for k, x in enumerate(seq):
    free = [m for m in range(1, N + 1) if not inS[m]]
    Z = [m for m in free if J[m] == 0]
    Zs = set(Z)
    blk = sum(1 for m in Z if (m + 1) in Zs or (m - 1) in Zs)
    rows.append((len(Z) / len(free), blk / len(Z), sum(abs(J[m]) for m in free) / len(free),
                 max(abs(J[m]) for m in free)))
    inS[x] = 1
    for q in range(x // 2 + 1, x): J[q] += 1
    for q in range(x + 1, (N + x) // 2 + 1): J[q] -= 1
seg = N // 8
for s in range(0, N, seg):
    r = rows[s:s + seg]
    print("k/N in [%.3f,%.3f): V/f %.3f  zeros in blocks %.3f  mean|J| %.2f  max|J| %d" % (
        s / N, (s + seg) / N, sum(a[0] for a in r) / seg, sum(a[1] for a in r) / seg,
        sum(a[2] for a in r) / seg, max(a[3] for a in r)))

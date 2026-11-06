import sys, math
# analyze.py path N : per-step loss log((N-k)/V), sigma_J over free panels, max discrepancy, by time segment
f = sys.argv[1]; N = int(sys.argv[2]); seq = [int(l) for l in open(f)]
J = [0] * (N + 2); inS = [0] * (N + 2); rows = []
for k, x in enumerate(seq):
    free = [m for m in range(1, N + 1) if not inS[m]]
    V = sum(1 for m in free if J[m] == 0)
    vals = [J[m] for m in free]; mu = sum(vals) / len(vals)
    sd = math.sqrt(sum((v - mu) ** 2 for v in vals) / len(vals))
    P = 0; D = 0
    for y in range(1, N + 1):
        P += inS[y]; D = max(D, abs(P - k * y / N))
    rows.append((k, V, N - k, math.log((N - k) / V), sd, D, max(abs(v) for v in vals)))
    assert J[x] == 0
    inS[x] = 1
    for q in range(x // 2 + 1, x): J[q] += 1
    for q in range(x + 1, (N + x) // 2 + 1): J[q] -= 1
seg = 8
for s in range(0, N, N // seg):
    r = rows[s:s + N // seg]
    print("k=%4d..%4d  mean loss %.3f  mean V/(N-k) %.3f  mean sdJ %.2f  mean disc %.2f  max|J| %d" % (
        s, s + N // seg - 1, sum(a[3] for a in r) / len(r), sum(a[1] / a[2] for a in r) / len(r),
        sum(a[4] for a in r) / len(r), sum(a[5] for a in r) / len(r), max(a[6] for a in r)))
print("total deficit", sum(a[3] for a in rows))

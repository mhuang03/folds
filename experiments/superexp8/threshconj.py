# threshconj.py: compare the conjectured parity-tree threshold (PROOFS.txt 3.2) with the data.
import glob


def conj(q):
    best = None
    k = 4
    while (1 << (k - 1)) + 1 <= q // 2:
        P = 1 << k
        r = q % P
        T = None
        if P - (P >> 3) < r <= P - (P >> 4):
            T = (P >> 1) + 1
        elif (P >> 4) <= r < (P >> 3):
            T = (P >> 1) + r + 1
        if T is not None and T <= q // 2 and (best is None or T < best):
            best = T
        k += 1
    return best


bad = 0; n = 0
for f in sorted(glob.glob('thresh_*.out')):
    for line in open(f):
        q, a, b = line.split()
        q = int(q); a = None if a == 'None' else int(a)
        n += 1
        if conj(q) != a:
            bad += 1
            print('mismatch', q, a, conj(q))
print(n, 'values,', bad, 'mismatches')

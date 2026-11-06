# Compare "n theta(n) mod 2^61-1" lines (window_mod.bin output, file argv[1]) with the b-file.
import sys, os
P = (1 << 61) - 1
here = os.path.dirname(os.path.abspath(__file__))
th = {int(a): int(b) for a, b in (l.split() for l in open(os.path.join(here, 'data/b003407.txt')))}
ok = bad = 0
for line in open(sys.argv[1]):
    n, v = map(int, line.split()[:2])
    if n in th:
        if th[n] % P == v: ok += 1
        else: bad += 1; print("MISMATCH", n)
print(f"checked {ok + bad} values, {bad} mismatches")

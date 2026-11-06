# Compare residue files written by theta.bin ("# p1 .. pK" header, then "n r1 .. rK") with
# the OEIS b-file (n <= 200) and with ../symratio/data/theta_exact.txt (n <= 300).
#   python3 checkres.py FILE...
import sys, os
here = os.path.dirname(os.path.abspath(__file__))
ref = {}
for fn in ('../symratio/data/b003407.txt', '../symratio/data/theta_exact.txt'):
    for l in open(os.path.join(here, fn)):
        a, b = l.split(); ref[int(a)] = int(b)
ok = bad = 0
for fn in sys.argv[1:]:
    ps = None
    for l in open(fn):
        f = l.split()
        if f[0] == '#': ps = list(map(int, f[1:])); continue
        n = int(f[0])
        if n not in ref: continue
        for p, v in zip(ps, map(int, f[1:])):
            if ref[n] % p == v: ok += 1
            else:
                bad += 1
                if bad < 10: print("MISMATCH n=%d p=%d" % (n, p))
print("checked %d residues, %d mismatches" % (ok + bad, bad))

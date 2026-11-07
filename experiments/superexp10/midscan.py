"""midscan.py qlo qhi budget [nus]: chains x ++ M ++ rev(sig x) with a 3-element middle block
M = ordering of {a, sig a, t0} (pal.c with the a argument), every a; odd q, nu = 3 mod 4 and
mirrors (the residues without palindromic chains).  Prints the middle pairs a that work."""
import sys
import subprocess

qlo, qhi, bud = map(int, sys.argv[1:4])
for q in range(qlo | 1, qhi + 1, 2):
    for nu in range(q):
        if (nu % 4 == 1) or ((q - nu) % 4 == 1):
            continue
        if len(sys.argv) > 4 and nu not in map(int, sys.argv[4].split(",")):
            continue
        t0 = [t for t in range(1, q + 1) if (nu - t) % q + 1 == t][0]
        good, unk = [], []
        for a in range(1, q + 1):
            b = (nu - a) % q + 1
            if a == t0 or b < a:
                continue
            out = subprocess.run(["./pal", str(q), str(nu), "0", str(bud), str(a)],
                                 capture_output=True, text=True).stdout
            if "res=OK" in out:
                good.append(a)
            elif "BUDGET" in out:
                unk.append(a)
        print(q, nu, "t0=%d" % t0, "ok:", good, "budget:", unk, flush=True)

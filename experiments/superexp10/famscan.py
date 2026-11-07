"""famscan.py qlo qhi K budget: for odd q, 1 <= nu, K nu < q, which dilation-2 transversal
families admit a palindromic chain (pal.c, mode 1).  Prints q nu followed by the families
(a,b) solved: '+' solved, '?' budget, '-' none."""
import sys
import subprocess
from trans import families

qlo, qhi, K, bud = map(int, sys.argv[1:5])
for q in range(qlo | 1, qhi + 1, 2):
    for nu in range(1, q):
        if K * nu >= q:
            break
        marks = []
        for key, T in sorted(families(q, nu).items()):
            out = subprocess.run(["./pal", str(q), str(nu), "1", str(bud)],
                                 input=" ".join(map(str, T)), capture_output=True,
                                 text=True).stdout
            marks.append("+" if "res=OK" in out else ("?" if "BUDGET" in out else "-"))
        print(q, nu, "".join(marks), flush=True)

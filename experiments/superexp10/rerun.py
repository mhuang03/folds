"""rerun.py infile budget: rerun the predicted-but-unsolved cases of famscan output (nu > 1)
with a larger budget."""
import sys
import subprocess
from trans import families

bud = sys.argv[2]
for line in open(sys.argv[1]):
    q, nu, marks = line.split()
    q, nu = int(q), int(nu)
    pred = (nu % 4 == 1) or ((q - nu) % 4 == 1)
    if not pred or "+" in marks or nu == 1:
        continue
    res = []
    for key, T in sorted(families(q, nu).items()):
        out = subprocess.run(["./pal", str(q), str(nu), "1", bud], input=" ".join(map(str, T)),
                             capture_output=True, text=True).stdout
        res.append("+" if "res=OK" in out else ("?" if "BUDGET" in out else "-"))
        if "res=OK" in out:
            break
    print(q, nu, "".join(res), flush=True)

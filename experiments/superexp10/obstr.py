"""obstr.py qlo qhi budget: exhaustive palindromic-chain search (pal.c mode 0) for odd q, all nu;
compares with the predicted condition  nu = 1 (mod 4)  or  q - nu = 1 (mod 4)."""
import sys
import subprocess

qlo, qhi, bud = map(int, sys.argv[1:4])
for q in range(qlo | 1, qhi + 1, 2):
    row = []
    for nu in range(q):
        out = subprocess.run(["./pal", str(q), str(nu), "0", str(bud)], capture_output=True,
                             text=True).stdout
        res = "OK" if "res=OK" in out else ("BUDGET" if "BUDGET" in out else "NONE")
        pred = (nu % 4 == 1) or ((q - nu) % 4 == 1)
        flag = "" if (res == "OK") == pred else ("?" if res == "BUDGET" else "!")
        row.append(f"{nu}:{res[0]}{flag}")
    print(q, " ".join(row), flush=True)

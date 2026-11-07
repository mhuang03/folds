"""famrun.py q nu [budget]: run pal.c on each dilation-2 transversal family."""
import sys
import subprocess
from trans import families

q, nu = int(sys.argv[1]), int(sys.argv[2])
bud = sys.argv[3] if len(sys.argv) > 3 else "2000000"
for key, T in families(q, nu).items():
    out = subprocess.run(["./pal", str(q), str(nu), "1", bud], input=" ".join(map(str, T)),
                         capture_output=True, text=True, timeout=600).stdout.strip()
    print(key, out[:200])

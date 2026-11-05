"""oeis.py FILE COL NFROM NTO [label]: look up a column of a data file in the OEIS."""
import json
import subprocess
import sys

fn, col, a, b = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
label = sys.argv[5] if len(sys.argv) > 5 else fn
vals = {}
for l in open(fn):
    t = l.split()
    if len(t) > col and t[0].isdigit():
        vals[int(t[0])] = t[col]
seq = ','.join(vals[n] for n in range(a, b + 1))
out = subprocess.run(['curl', '-s', f'https://oeis.org/search?q={seq}&fmt=json'],
                     capture_output=True, text=True).stdout
try:
    d = json.loads(out)
except Exception:
    d = None
hits = [(f"A{r['number']:06d}", r['name'][:90]) for r in d] if isinstance(d, list) else []
print(label, seq, '->', hits[:5] if hits else 'no match')

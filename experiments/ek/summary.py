"""summary.py FILE...: one line per file: N -> number of dead (and unresolved) sets, up to mirror."""
import sys, re

for fn in sys.argv[1:]:
    rows = []
    for line in open(fn):
        m = re.match(r'N=(\d+) k=(\d+) lo=(\d+): sets\(up to mirror\)=(\d+) G=(\d+) dead=(\d+) unresolved=(\d+)', line)
        if m:
            N, k, lo, s, g, d, u = map(int, m.groups())
            rows.append((N, d, u, s))
    if not rows:
        continue
    print(f"{fn} (k={k}, lo={lo}): N = {rows[0][0]}..{rows[-1][0]}, sets examined {sum(r[3] for r in rows)}")
    print("   dead:", " ".join(f"{N}:{d}" + (f"(+{u}?)" if u else "") for N, d, u, s in rows if d or u) or "none")

"""ghost1.py: {1, N} (N odd): which even e allow ordering O' + {e} on background {1, N}
with the other evens absent (phase 1 of the ghost reduction)."""
import subprocess
import sys
lo, hi = int(sys.argv[1]), int(sys.argv[2])
for N in range(lo, hi + 1, 2):
    good = []
    for e in range(2, N, 2):
        ev = [x for x in range(2, N, 2) if x != e]
        r = subprocess.run(['./bg', str(N), '1', str(N), 'z'] + list(map(str, ev)),
                           capture_output=True, text=True).stdout.strip()
        if 'not' not in r:
            good.append(e)
    print(N, good, flush=True)

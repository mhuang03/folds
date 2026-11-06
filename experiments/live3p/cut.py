# cut.py IN OUT MARKER [EXTRA]: copy IN to OUT up to (not including) the first line starting
# with MARKER, plus EXTRA more lines, then close the namespace (for bisecting slow checks).
import sys
src, dst, marker = sys.argv[1:4]
extra = int(sys.argv[4]) if len(sys.argv) > 4 else 0
L = open(src).read().split('\n')
i = next(k for k, l in enumerate(L) if l.startswith(marker))
open(dst, 'w').write('\n'.join(L[:i + extra]) + '\nend Folds.Live3p\n')

"""splice.py FILE START END NEW: replace the text of FILE from the first line starting with START
up to (not including) the first later line starting with END by the contents of NEW."""
import sys

path, start, end, new = sys.argv[1:5]
lines = open(path).read().split('\n')
a = next(i for i, l in enumerate(lines) if l.startswith(start))
b = next(i for i in range(a + 1, len(lines)) if lines[i].startswith(end))
lines[a:b] = open(new).read().rstrip('\n').split('\n') + ['']
open(path, 'w').write('\n'.join(lines))

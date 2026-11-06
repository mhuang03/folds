# bisect.py START END OUT: write OUT = the header of Folds/Live3t.lean (up to the first section)
# plus the part between the markers START and END (substrings of section headers / docstrings),
# for compiling one block at a time (memory debugging).
import sys, os
F = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'Folds', 'Live3t.lean')
s = open(F).read()
head = s[:s.index('/-! ## The complement of a near copy')]
i = s.index(sys.argv[1]); j = s.index(sys.argv[2], i + 1)
open(sys.argv[3], 'w').write(head + s[i:j] + '\nend Live3t\nend Folds\n')

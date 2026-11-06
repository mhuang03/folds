# bisect.py FILE THEOREM OUT K: copy FILE up to the end of THEOREM into OUT, replacing the K-th
# top-level `have ... := by` block of THEOREM (K = 0: none) by `sorry` (debugging aid).
import sys
src, thm, out, k = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
s = open(src).read()
i = s.index('theorem ' + thm)
j = s.find('\n/--', i)
body = s[i:j].split('\n')
res, cnt, skip = [], 0, False
for ln in body:
    if skip:
        if ln.startswith('    '): continue
        skip = False
    if ln.startswith('  have ') and ln.rstrip().endswith(':= by'):
        cnt += 1
        if cnt == k:
            res.append(ln + ' sorry'); skip = True; continue
    res.append(ln)
open(out, 'w').write(s[:i] + '\n'.join(res) + '\nend Live3s\nend Folds\n')

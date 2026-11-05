"""certlean.py certs.txt: the Lean block (tables `certs<q>`, their `decide` checks, `certTbl`)
for Folds/Live4.lean, from the output of certtbl.py.  Tables with more than CH entries are
split into chunks (one `decide` per chunk keeps the kernel check small)."""
import sys

import os
CH = int(os.environ.get("CH", "40"))
by = {}
for line in open(sys.argv[1]):
    w = list(map(int, line.split()))
    if w:
        by.setdefault(w[0], []).append((w[1], w[2:]))
names = []
out = []
for q in sorted(by):
    ent = by[q]
    for c in range(0, len(ent), CH):
        name = 'certs%d_%d' % (q, c // CH)
        names.append(name)
        body = ',\n  '.join('(%d, %d, [%s])' % (q, nu, ','.join(map(str, p))) for nu, p in ent[c:c + CH])
        out.append('def %s : List (Nat × Nat × List Nat) :=\n  [%s]\n' % (name, body))
        out.append('theorem %s_ok : %s.all (fun e => decide (fullOK e)) = true := by decide +kernel\n'
                   % (name, name))
out.append('/-- All certificates. -/\ndef certTbl : List (Nat × Nat × List Nat) :=\n  ' +
           ' ++ '.join(names) + '\n')
out.append('theorem certTbl_ok : certTbl.all (fun e => decide (fullOK e)) = true := by\n'
           '  simp only [certTbl, List.all_append, ' +
           ', '.join(n + '_ok' for n in names) + ', Bool.and_self]\n')
print('\n'.join(out))

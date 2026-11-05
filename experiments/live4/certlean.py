"""certlean.py certs.txt: the Lean block of certificates for Folds/Live4.lean, one theorem
`cert_<q>_<i> : fullOK (q, nu, pi) := fullOK_of_certB (by decide +kernel)` per line "q nu pi_1 ... pi_q" of certs.txt (output of
certtbl.py).  One `decide` per certificate keeps every kernel check small (the memory is
released between declarations; a chunk of 40 certificates in one `decide` needs ~2 GB more).
Each certificate gives `Gd.cert cert_<q>_<i> rfl : Gd q nu pi_1`."""
import sys

cnt = {}
out = []
for line in open(sys.argv[1]):
    w = list(map(int, line.split()))
    if not w:
        continue
    q, nu, pi = w[0], w[1], w[2:]
    i = cnt.get(q, 0)
    cnt[q] = i + 1
    out.append('theorem cert_%d_%d : fullOK (%d, %d, [%s]) :=\n  fullOK_of_certB (by decide +kernel)'
               % (q, i, q, nu, ','.join(map(str, pi))))
print('\n'.join(out))

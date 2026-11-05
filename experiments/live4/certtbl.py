"""certtbl.py BIN q1 q2 > certs.txt: certificates `(q, nu, pi)` for the table `certTbl` of
Folds/Live4.lean, for q1 <= q <= q2.  BIN is the compiled fullcert.c.  For each q, the
(nu, t) not yet good in the closure of covlean4.py (with the certificates of smaller q
already added) are visited in order; for each one a certificate from fullcert is added and
the closure under sig / mirror is recomputed, so one certificate is kept per orbit.
Output: one line "q nu x_1 ... x_q" per certificate."""
import subprocess
import sys

sys.path.insert(0, __file__.rsplit('/', 1)[0])
import covlean4 as C

BIN, q1, q2 = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
out = []
for q in range(q1, q2 + 1):
    S = set(C.good_set(q))
    need = [(nu, t) for nu in range(q) for t in range(1, q + 1)
            if not C.exc(q, nu, t) and (nu, t) not in S]
    if not need:
        continue
    res = subprocess.run([BIN, str(q)], capture_output=True, text=True).stdout.split('\n')
    cert = {}
    for line in res:
        w = line.split()
        if len(w) < 3 or w[2] == '-':
            continue
        cert[(int(w[0]), int(w[1]))] = list(map(int, w[2:]))
    n = 0
    for (nu, t) in need:
        if (nu, t) in S or (nu, t) not in cert:
            continue
        out.append('%d %d %s' % (q, nu, ' '.join(map(str, cert[(nu, t)]))))
        n += 1
        S.add((nu, t))
        while True:
            new = set()
            for (a, b) in S:
                new.add((a, C.sig(q, a, b)))
                new.add(((q - a) % q, q + 1 - b))
            if new <= S:
                break
            S |= new
    print('q', q, 'certificates', n, 'good now', len(S), 'of', q * q, file=sys.stderr)
    C.G[q] = S
print('\n'.join(out))

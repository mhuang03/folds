# mkE.py N1 N2 [chunk] > out.lean : certificates for Folds/EkStar3.lean from the hint files
# bin/hE/<N>.txt (written by `bin/hintsE N 3`; lines "a b c sign hint...").
# For each N and smallest element a: the b-range (a, N - 1] is cut into chunks [b0, b1) of at
# most `chunk` cost units; each chunk is one packed number (Live3q.decH) with its kernel check
# `che_N_a_k` (chkE N a b0 b1); then `cove_N_a` (all b) and `cove_N : CovQE N`.
import sys
from collections import defaultdict

def enc_hint(sign, f):
    """base-128 digit list of one hint (see Live3q.decH)."""
    m = 1 if sign == '-' else 0
    if f[0] == 'W':
        xs = [int(t) for t in f[1:]]
        return [1 + m, len(xs)] + xs
    if f[0] == 'S':
        xs = [int(t) for t in f[2:]]
        return [3 + m, int(f[1]), len(xs)] + xs
    if f[0] == 'T':
        return [5 + m] + [int(t) for t in f[1:8]]
    raise ValueError(f)

def pack(ds):
    for d in ds: assert 0 <= d < 128
    w = 0
    for d in reversed(ds): w = w * 128 + d
    return w

def weight(f):
    return 8 if f[0] == 'W' else 1

def chain(names, trans, base):
    t = '%s %s' % (base, names[-1])
    for nm in reversed(names[:-1]):
        t = '%s (%s %s) (%s)' % (trans, base, nm, t)
    return t

def gen(N, chunk, out):
    by_ab = defaultdict(list)
    for line in open('bin/hE/%d.txt' % N):
        f = line.split()
        if not f: continue
        if f[3] == '?': raise SystemExit('FAIL %s' % line)
        by_ab[(int(f[0]), int(f[1]))].append((enc_hint(f[3], f[4:]), weight(f[4:])))
    out.write('/-! ### `N = %d` -/\n\n' % N)
    if N <= 4:
        out.write('theorem cove_%d : CovQE %d := CovQE.of_small (by decide)\n\n' % (N, N))
        return
    alist = []
    for a in range(2, N - 2):
        chunks = []; cur = []; b0 = a + 1; w = 0
        for b in range(a + 1, N):
            hs = by_ab.get((a, b), [])
            if cur and w + sum(x[1] for x in hs) > chunk:
                chunks.append((b0, b, cur)); cur = []; b0 = b; w = 0
            cur += [x[0] for x in hs]; w += sum(x[1] for x in hs)
        chunks.append((b0, N, cur))
        for k, (lo, hi, hs) in enumerate(chunks):
            code = pack([d for h in hs for d in h])
            out.write('theorem che_%d_%d_%d : chkE %d %d %d %d (decH %d %d) = true := by decide +kernel\n'
                      % (N, a, k, N, a, lo, hi, len(hs) + 1, code))
        out.write('theorem cove_%d_%d : CovBE %d %d %d %d :=\n  %s\n\n' % (N, a, N, a, a + 1, N,
                  chain(['che_%d_%d_%d' % (N, a, k) for k in range(len(chunks))], 'CovBE.trans', 'CovBE.of_chk')))
        alist.append(a)
    out.write('theorem cove_%d : CovQE %d :=\n  CovQE.of_covAE (%s)\n\n' % (N, N,
              chain(['cove_%d_%d' % (N, a) for a in alist], 'CovAE.trans', 'CovAE.one')))

if __name__ == '__main__':
    n1, n2 = int(sys.argv[1]), int(sys.argv[2])
    chunk = int(sys.argv[3]) if len(sys.argv) > 3 else 40
    for N in range(n1, n2 + 1):
        gen(N, chunk, sys.stdout)

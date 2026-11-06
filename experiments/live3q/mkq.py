# mkq.py N1 N2 [maxdepth] [chunk] > out.lean : certificates for Folds/Live3q.lean from ./hints
# For each N and smallest element a: the b-range (a, N] is cut into chunks [b0, b1) with at most
# `chunk` hints; each chunk is one packed number (decH) with its kernel check `chq_N_a_k`
# (chkR N a b0 b1); then `cov_N_a` (all b) and `cov_N : CovQ N`.
import subprocess, sys
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
    # rough kernel cost of a hint (witness orderings are the expensive ones)
    return 8 if f[0] == 'W' else 1

def gen(N, maxd, chunk, out):
    res = subprocess.run(['./hints', str(N), str(maxd)], capture_output=True, text=True)
    sys.stderr.write(res.stderr)
    by_ab = defaultdict(list)
    for line in res.stdout.split('\n'):
        f = line.split()
        if not f: continue
        if f[3] == '?': raise SystemExit('FAIL %s' % line)
        by_ab[(int(f[0]), int(f[1]))].append((enc_hint(f[3], f[4:]), weight(f[4:])))
    out.write('/-! ### `N = %d` -/\n\n' % N)
    alist = []
    for a in range(1, N - 1):
        # chunks of b
        chunks = []; cur = []; b0 = a + 1; w = 0
        for b in range(a + 1, N + 1):
            hs = by_ab.get((a, b), [])
            if cur and w + sum(x[1] for x in hs) > chunk:
                chunks.append((b0, b, cur)); cur = []; b0 = b; w = 0
            cur += [x[0] for x in hs]; w += sum(x[1] for x in hs)
        chunks.append((b0, N + 1, cur))
        for k, (lo, hi, hs) in enumerate(chunks):
            code = pack([d for h in hs for d in h])
            out.write('theorem chq_%d_%d_%d : chkR %d %d %d %d (decH %d %d) = true := by decide +kernel\n'
                      % (N, a, k, N, a, lo, hi, len(hs) + 1, code))
        def chain(names, trans, base):
            t = '%s %s' % (base, names[-1])
            for nm in reversed(names[:-1]):
                t = '%s (%s %s) (%s)' % (trans, base, nm, t)
            return t
        out.write('theorem cov_%d_%d : CovB %d %d %d %d :=\n  %s\n\n' % (N, a, N, a, a + 1, N + 1,
                  chain(['chq_%d_%d_%d' % (N, a, k) for k in range(len(chunks))], 'CovB.trans', 'CovB.of_chk')))
        alist.append(a)
    out.write('theorem cov_%d : CovQ %d :=\n  CovQ.of_covA (%s)\n\n' % (N, N,
              chain(['cov_%d_%d' % (N, a) for a in alist], 'CovA.trans', 'CovA.one')))

if __name__ == '__main__':
    n1, n2 = int(sys.argv[1]), int(sys.argv[2])
    maxd = int(sys.argv[3]) if len(sys.argv) > 3 else 3
    chunk = int(sys.argv[4]) if len(sys.argv) > 4 else 60
    for N in range(n1, n2 + 1):
        gen(N, maxd, chunk, sys.stdout)

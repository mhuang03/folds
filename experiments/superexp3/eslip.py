"""E-type ("aligned") slips.  N = 2n, E subset [1, n], e_i = [i in E],
   f_i = 2i - e_i,  s_i = 2i - 1 + e_i   (X = f([n]) takes one panel of every pair {2i-1, 2i}).
Claimed lemma: (f_tau, s_sigma) is valid iff tau, sigma valid n-sequences and
   for every j in [n] and child c in {q(j) = 2j mod* n, p(j) = (2j-1) mod* n} with e_j != e_c:
     c = q(j):  c in E  -> tau: j before c;      j in E -> sigma: c before j
     c = p(j):  j in E  -> tau: j before c;      c in E -> sigma: c before j
Exhaustive check for n <= nmax: every E, every tau, sigma in V_n (sufficiency), and
necessity among strip-valid tau, sigma.
Usage: python3 eslip.py nmax"""
import sys, itertools

def valid_seq(seq, N):
    placed = [0] * (N + 2)
    for m in seq:
        r = min(m - 1, N - m)
        if sum(placed[m - d] for d in range(1, r + 1)) != sum(placed[m + d] for d in range(1, r + 1)):
            return False
        placed[m] = 1
    return True

def gen(n):
    out = []
    def rec(seq, used):
        if len(seq) == n:
            out.append(tuple(seq)); return
        for m in range(1, n + 1):
            if not used[m]:
                r = min(m - 1, n - m)
                if sum(used[m - d] for d in range(1, r + 1)) == sum(used[m + d] for d in range(1, r + 1)):
                    used[m] = 1; seq.append(m); rec(seq, used); seq.pop(); used[m] = 0
    rec([], [0] * (n + 2))
    return out

def ms(x, n):
    return (x - 1) % n + 1

def conds(E, n):
    """list of (which, a, b): 'T' = tau places a before b, 'S' = sigma places a before b"""
    out = []
    for j in range(1, n + 1):
        q, p = ms(2 * j, n), ms(2 * j - 1, n)
        ej = j in E
        if (q in E) != ej:
            if q in E: out.append(('T', j, q))
            else: out.append(('S', q, j))
        if (p in E) != ej:
            if ej: out.append(('T', j, p))
            else: out.append(('S', p, j))
    return out

def main():
    nmax = int(sys.argv[1])
    for n in range(1, nmax + 1):
        V = gen(n)
        pos = {t: {m: i for i, m in enumerate(t)} for t in V}
        bad = 0; tot = 0; nec_bad = 0
        for bits in range(1 << n):
            E = {i + 1 for i in range(n) if bits >> i & 1}
            f = {i: 2 * i - (i in E) for i in range(1, n + 1)}
            s = {i: 2 * i - 1 + (i in E) for i in range(1, n + 1)}
            C = conds(E, n)
            # tau-conditions and sigma-conditions are separable: validity of the first block
            # depends only on tau, the second only on sigma (first block complete).
            for t in V:
                okc = all(pos[t][a] < pos[t][b] for w, a, b in C if w == 'T')
                for sg in V:
                    oks = all(pos[sg][a] < pos[sg][b] for w, a, b in C if w == 'S')
                    v = valid_seq([f[x] for x in t] + [s[x] for x in sg], 2 * n)
                    tot += 1
                    if (okc and oks) != v:
                        if okc and oks: bad += 1
                        else: nec_bad += 1
        print(f"n={n}: a(n)={len(V)} checks={tot} sufficiency failures={bad} necessity failures={nec_bad}", flush=True)

if __name__ == '__main__':
    main()

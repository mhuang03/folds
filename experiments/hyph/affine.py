"""affine.py q : do affine maps t -> m t + c (mod q, on labels 1..q) send GoodL(q, nu) orders into
GoodL(q, nu')?  Prints (nu, m, c, nu', fraction of orders mapped into GoodL(q, nu'))
for the best nu' when the fraction is large."""
import sys
q = int(sys.argv[1])
thr = float(sys.argv[2]) if len(sys.argv) > 2 else 0.5

def reach(t):
    return min(t - 1, q - t)

def valid_step(S, t):
    r = reach(t)
    return sum(1 for k in range(1, r + 1) if (t - k) in S) == sum(1 for k in range(1, r + 1) if (t + k) in S)

def sig(nu, t):
    return (nu - t) % q + 1

def good_orders(nu):
    res = []
    dead = set()
    def dfs(seq, S, T):
        if len(seq) == q:
            res.append(tuple(seq)); return True
        key = frozenset(S)
        if key in dead: return False
        any_ = False
        for t in range(1, q + 1):
            if t in S: continue
            if valid_step(S, t) and valid_step(T, sig(nu, t)):
                S.add(t); T.add(sig(nu, t)); seq.append(t)
                if dfs(seq, S, T): any_ = True
                seq.pop(); S.discard(t); T.discard(sig(nu, t))
        if not any_: dead.add(key)
        return any_
    dfs([], set(), set())
    return res

G = {nu: good_orders(nu) for nu in range(q)}
S = {nu: set(G[nu]) for nu in range(q)}
for nu in range(q):
    print('nu', nu, len(G[nu]))
for nu in range(q):
    for m in range(2, q - 1):
        for c in range(q):
            imgs = [tuple((m * (t - 1) + c) % q + 1 for t in p) for p in G[nu]]
            for nu2 in range(q):
                f = sum(1 for p in imgs if p in S[nu2]) / max(1, len(imgs))
                if f >= thr:
                    print('nu', nu, 'm', m, 'c', c, '->', nu2, round(f, 3))

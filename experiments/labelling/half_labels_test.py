"""Per-half claim: with P = [1,h], h = (N+1)//2, Q = the rest, kP = #distinct labels on P,
kQ = #distinct labels on Q:  h <= 2^kP - 1  and  N - h <= 2^kQ - 1 ?
Also with the top halves P0 = [1, h//2], Q0 = last (N-h)//2 panels:  does P0 miss a label of P?"""
import glob, sys
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    h = (N + 1) // 2; hp = N - h
    st = dict(n=0, P=0, Q=0, P0miss=0, Q0miss=0); ex = {}
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [int(ch) for ch in s]
        P, Q = c[:h], c[h:]
        kP, kQ = len(set(P)), len(set(Q))
        st['n'] += 1
        okP = h <= 2 ** kP - 1; okQ = hp <= 2 ** kQ - 1
        st['P'] += okP; st['Q'] += okQ
        if not okP: ex.setdefault('P', s)
        if not okQ: ex.setdefault('Q', s)
        P0 = c[:h // 2]; Q0 = c[N - hp // 2:]
        st['P0miss'] += len(set(P0)) < kP; st['Q0miss'] += len(set(Q0)) < kQ
    print(N, t, st, ex)

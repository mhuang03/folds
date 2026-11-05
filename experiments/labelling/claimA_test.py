"""Claim A' for admissible labellings: #{x : M - x <= n, c(x) < v} <= #{1 <= g <= n : pc(g) <= v}
for all v, n (M = N+1).  Reports the first violations, per file."""
import glob, sys
files = sys.argv[1:] or sorted(glob.glob('all_*_*.txt'))
pc = lambda g: bin(g).count('1')
for f in files:
    N, t = map(int, f.split('/')[-1][4:-4].split('_'))
    M = N + 1
    bad = 0; ex = None; worst = {}
    for s in open(f):
        s = s.strip()
        if len(s) != N: continue
        c = [None] + [int(ch) for ch in s]
        ok = True
        for v in range(1, t + 1):
            cnt = 0; bound = 0
            for n in range(1, N + 1):
                cnt += c[M - n] < v; bound += pc(n) <= v
                if cnt > bound:
                    ok = False
                    key = (v, n)
                    worst[key] = worst.get(key, 0) + 1
        if not ok:
            bad += 1
            if ex is None: ex = s
    print(N, t, 'violations', bad, ex, sorted(worst.items())[:8])

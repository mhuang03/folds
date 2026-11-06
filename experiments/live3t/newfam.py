# newfam.py N0 N1: how much of the residual of Live3q's rules (bin/c<N>.txt, canonical
# orientation) the parametric families of Folds/Live3t.lean settle:
#   one_b_N: {1, b, N}, N = 2 mod 4;  one_three_N: {1, 3, N} and its mirror {1, N - 2, N},
#   N = 1 mod 4;  also Live3r's chiX family {1, 2k, N}, N odd (coReach_one_even_N).
import sys, os
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'bin')
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    fn = os.path.join(D, 'c%d.txt' % N)
    if not os.path.exists(fn): continue
    T = [tuple(map(int, l.split()[1:4])) for l in open(fn) if len(l.split()) > 4]
    fb = sum(1 for (a, b, c) in T if N % 4 == 2 and a == 1 and c == N)
    f3 = sum(1 for (a, b, c) in T if N % 4 == 1 and a == 1 and c == N and b in (3, N - 2))
    fx = sum(1 for (a, b, c) in T if N % 2 == 1 and a == 1 and c == N and b % 2 == 0)
    print('N=%d residual %d: one_b_N %d, one_three_N %d, chiX %d' % (N, len(T), fb, f3, fx))

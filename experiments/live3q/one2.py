# one2.py NMIN NMAX A B: for the sets {A, B, c}, which c are covered by transfer / S2, and which are left (ana output)
import subprocess, sys
A, Bv = int(sys.argv[3]), int(sys.argv[4])
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    out = subprocess.run(['./ana', str(N), str(N), '2'], capture_output=True, text=True).stdout.split('\n')
    T = {}; L = set()
    for l in out:
        f = l.split()
        if len(f) >= 5 and f[0] in ('T', 'S2', 'left') and f[2] == str(A) and f[3] == str(Bv):
            if f[0] == 'T': T[int(f[4])] = f[5]
            elif f[0] == 'S2': T[int(f[4])] = 'S2'
            else: L.add(int(f[4]))
    print(N, 'left', sorted(L), 'T', sorted(T.items()))

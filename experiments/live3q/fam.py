# fam.py N1 N2 maxd A B: the hints of ./hints for the triples (A, B, c)
import subprocess, sys
maxd = sys.argv[3]; A, B = sys.argv[4], sys.argv[5]
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    out = subprocess.run(['./hints', str(N), maxd], capture_output=True, text=True).stdout
    for line in out.split('\n'):
        f = line.split()
        if len(f) > 4 and f[0] == A and f[1] == B:
            print(N, ' '.join(f[2:]) if f[4] != 'W' else ' '.join(f[2:5]))

# chkall.py N1 N2: generate and compile the kernel checks of the rcov hints (rcall.txt) for
# each N in [N1, N2]; prints errors (none expected) and time / peak memory per N.
import subprocess, sys, os
d = os.path.dirname(os.path.abspath(__file__))
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    f = os.path.join(d, 'chk%d.lean' % N)
    subprocess.run(['python3', os.path.join(d, 'genchk.py'), os.path.join(d, 'rcall.txt'), f, str(N), str(N)], check=True)
    r = subprocess.run(['python3', os.path.join(d, 'memtime.py'), f], capture_output=True, text=True)
    print(N, r.stdout.strip().replace('\n', ' | ')[-400:])
    sys.stdout.flush()
    os.remove(f)

"""trylean.py N [N ...]: generate the mixedB certificate theorem for each N (gencert), put it in a
scratch Lean file importing Folds.Live8, elaborate it, report time and peak RSS per N.
Usage: python3 trylean.py SCRATCHDIR N1 N2 ..."""
import os
import resource
import subprocess
import sys
import time

here = os.path.dirname(os.path.abspath(__file__))
root = os.path.abspath(os.path.join(here, '..', '..'))
scratch = sys.argv[1]
env = dict(os.environ)
env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env['PATH']
for a in sys.argv[2:]:
    N = int(a)
    if N == 0:
        body = ''
    else:
        body = subprocess.run([os.path.join(here, 'gencert'), str(N), str(N)], capture_output=True,
                              text=True).stdout
    fn = os.path.join(scratch, 'T%d.lean' % N)
    with open(fn, 'w') as f:
        f.write('import Folds.Live8\nnamespace Folds.Live8\n' + body + 'end Folds.Live8\n')
    t = time.time()
    r = subprocess.Popen(['lake', 'env', 'lean', fn], cwd=root, env=env,
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    out, err = r.communicate()
    ru = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024
    print(N, 'time %.1fs' % (time.time() - t), 'maxrss(cumulative max) %.0f MB' % ru,
          (out + err)[-500:].strip(), flush=True)

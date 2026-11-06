"""memtime.py FILE.lean: compile one Lean file with `lake env lean`, print output, time, peak RSS."""
import os
import resource
import subprocess
import sys
import time

env = dict(os.environ)
env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env['PATH']
t = time.time()
r = subprocess.run(['lake', 'env', 'lean', sys.argv[1]], capture_output=True, text=True, env=env)
print(r.stdout[-4000:], r.stderr[-2000:])
print('time %.1fs  maxrss %.0f MB' % (time.time() - t,
      resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024))

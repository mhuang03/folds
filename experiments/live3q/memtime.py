# memtime.py FILE: compile a Lean file with `lake env lean -M 3000`, report time and peak RSS
import subprocess, sys, time, resource, os
os.environ['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH']
t = time.time()
r = subprocess.run(['lake', 'env', 'lean', '-M', '3000', sys.argv[1]], capture_output=True, text=True,
                   cwd=os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..'))
dt = time.time() - t
rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024
print('time %.1f s, peak RSS %.0f MB, exit %d' % (dt, rss, r.returncode))
print((r.stdout + r.stderr)[:3000])

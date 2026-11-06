# memtime.py FILE: compile FILE with lean.sh, print wall time and peak RSS (MB)
import subprocess, sys, time, resource, os
t = time.time()
r = subprocess.run(['sh', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'lean.sh')] + sys.argv[1:],
                   capture_output=True, text=True)
print(r.stdout[-3000:], r.stderr[-3000:])
print('time %.1f s, peak %.0f MB' % (time.time() - t,
      resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss / 1024))

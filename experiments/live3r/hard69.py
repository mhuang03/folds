# hard69.py: long DFS runs for {1, 2, 67} in [69] (the one triple of the left list without a
# numerical completion found by leftchk.py), several candidate orders.
import subprocess, os
env = dict(os.environ, LIM='200000000')
for o in ['1', '69', '35', '17.5', '52', '2', '60', '10']:
    r = subprocess.run(['timeout', '900', './pfx', '69', o, '1', '2', '67'], capture_output=True, text=True, env=env).stdout.strip()
    print('ORD', o, r if r else 'TIMEOUT', flush=True)
    if r and not r.startswith('FAIL'):
        break

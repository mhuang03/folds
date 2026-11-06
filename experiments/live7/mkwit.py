"""mkwit.py N u v [seed] [limit]: run ./dfs and print the ordering of [N] minus {u, v} from scratch
(the reversed completion of the prefix [u, v]), checked in Python."""
import subprocess
import sys


def reach(N, m):
    return min(m - 1, N - m)


def semi_ok(N, l):
    S = set()
    for m in l:
        r = reach(N, m)
        if sum((m - d) in S for d in range(1, r + 1)) != sum((m + d) in S for d in range(1, r + 1)):
            return False
        S.add(m)
    return True


def witness(N, u, v, seed=1, limit=100000):
    out = subprocess.run(['./dfs', str(N), str(u), str(v), str(seed), str(limit)],
                         capture_output=True, text=True).stdout.strip()
    if out == 'FAIL':
        return None
    l = [int(x) for x in out.split(',')][::-1]
    assert sorted(l) == sorted(set(range(1, N + 1)) - {u, v})
    assert semi_ok(N, l)
    return l


if __name__ == '__main__':
    a = [int(x) for x in sys.argv[1:]]
    print(witness(*a))

"""Sign distribution: fixed points of block-swap involutions (Ruskey-type), N <= 13."""
import sys
from common import *

def main(Nmax):
    for N in range(2, Nmax + 1):
        D = 0; fp = [0, 0]; fps = [0, 0]; adapt = 0
        nswap_hist = {}
        for a in valid_seqs(N):
            s = sign(a); D += s
            nr = [near(N, a[i], a[i + 1]) for i in range(N - 1)]
            for off in (0, 1):
                if all(nr[i] for i in range(off, N - 1, 2)):
                    fp[off] += 1; fps[off] += s
            k = (N - 1) - sum(nr)
            nswap_hist[k] = nswap_hist.get(k, 0) + 1
        print(N, "a", A[N], "D", D, "fix(blocks 12|34..)", fp[0], fps[0], "fix(blocks 23|45..)", fp[1], fps[1],
              "far-adjacent-count hist", sorted(nswap_hist.items()))
        sys.stdout.flush()

main(int(sys.argv[1]) if len(sys.argv) > 1 else 11)

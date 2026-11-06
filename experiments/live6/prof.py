"""prof.py N x1 x2 ...: imbalance profile of X: for each panel, I_X(m) ('*' marks X)."""
import sys
from twoside import imb_all

N = int(sys.argv[1])
X = [int(a) for a in sys.argv[2:]]
ind, I = imb_all(N, X)
print(' '.join(f"{m}{'*' if ind[m] else ''}:{I[m]:+d}" for m in range(1, N + 1)))

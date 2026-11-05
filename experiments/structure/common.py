"""Shared helpers: load/compute g[S] (number of valid orderings of S as a prefix)."""
import os, subprocess
import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
CACHE = os.environ.get("GCACHE", os.path.join(HERE, ".cache"))


def g_array(N, mode="semi", par=0):
    os.makedirs(CACHE, exist_ok=True)
    fn = os.path.join(CACHE, f"{mode}_{par}_{N}.bin")
    if not os.path.exists(fn):
        exe = os.path.join(HERE, "dp")
        if not os.path.exists(exe):
            subprocess.check_call(["gcc", "-O2", "-o", exe, os.path.join(HERE, "dp.c")])
        subprocess.check_call([exe, str(N), mode, str(par), fn], stdout=subprocess.DEVNULL)
    return np.fromfile(fn, dtype=np.uint64)


def popcounts(N):
    return np.bitwise_count(np.arange(1 << N, dtype=np.uint64)).astype(np.int64)


def f_array(g, N):
    """completion counts f(S) = g(complement S) (reversal symmetry)."""
    full = (1 << N) - 1
    return g[full ^ np.arange(1 << N, dtype=np.uint64)]


def step_ok(S, m, N):
    D = min(m - 1, N - m)
    a = sum((S >> (m - d - 1)) & 1 for d in range(1, D + 1))
    b = sum((S >> (m + d - 1)) & 1 for d in range(1, D + 1))
    return a == b


A = [1, 2, 4, 10, 28, 96, 256, 1120, 4256, 17878, 70960, 383476, 1620328, 9167908,
     47821296, 276182312, 1481994716, 10084180418, 55082188120, 398874108930,
     2505681033958, 18168130281086, 119006527671252, 979730153850974,
     6564449510287388, 55581983250573500, 413109755332919448]

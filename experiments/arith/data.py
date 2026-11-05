"""a(N) for N = 1..33 (semi-symmetric fold sequences) and the self-dual counts."""
A = [1, 2, 4, 10, 28, 96, 256, 1120, 4256, 17878, 70960, 383476, 1620328, 9167908,
     47821296, 276182312, 1481994716, 10084180418, 55082188120, 398874108930,
     2505681033958, 18168130281086, 119006527671252, 979730153850974, 6564449510287388,
     55581983250573500, 413109755332919448, 3603074636066234798, 27545080998591561856,
     262878496654501774250, 2037247307316034896720, 20222490725552617395966,
     171668579369815966705184]
a = {i + 1: v for i, v in enumerate(A)}


def load_selfdual(path=None):
    import os
    path = path or os.path.join(os.path.dirname(__file__), "selfdual_out.txt")
    c = {}
    for line in open(path):
        if line.startswith("#") or not line.strip():
            continue
        n, v = line.split()[:2]
        c[int(n)] = int(v)
    return c

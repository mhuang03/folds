"""Classify pairs (m, m') by geometry and see where kappa = 0."""
import sys
from collections import defaultdict
from model2 import K
from pair import roles, radius

N = int(sys.argv[1])
cls = defaultdict(list)
for m in range(1, N + 1):
    for mp in range(m + 1, N + 1):
        rm, rmp = roles(N, m), roles(N, mp)
        if not rm or not rmp:
            continue
        Wm = set(rm) | {m}
        Wp = set(rmp) | {mp}
        O = Wm & Wp
        if not O:
            key = "disjoint"
        else:
            a = mp in Wm
            b = m in Wp
            # types of overlap elements (excluding centres)
            typ = sorted(set((rm.get(e, 0), rmp.get(e, 0)) for e in O - {m, mp}))
            key = "m'inWm=%d minWm'=%d WmsubWm'=%d Wm'subWm=%d types=%s" % (
                a, b, Wm <= Wp, Wp <= Wm, typ)
        k = K(N, m, mp)
        cls[key].append((m, mp, float(k)))
for key, v in sorted(cls.items()):
    nz = [x for x in v if x[2] != 0]
    print("%-75s n=%3d nonzero=%3d  e.g. %s" % (key, len(v), len(nz), (nz or v)[:3]))

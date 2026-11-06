"""Witness for the sharpness of Sharma's bound f(N) >= floor(N/2) - 6 at N = 26.

Construction (Theorem M): D = evens, the first C-entry is u = 1.  The D-entries after u
must avoid the values linked to 1, i.e. be >= 14: a suffix of a 3-AP-free permutation
sigma of the rescaled class [13] lying in the top 7 values {7..13} (G(13,7) = 6).  Then
  a = lift(sigma[:7]) ++ [1] ++ lift(sigma[7:]) ++ lift(tau[1:])
with tau any 3-AP-free permutation of [13] starting with 1.  The result is checked by
brute force here and in Lean (`SymStructure2.sharp_26`): a[0..6] even, a[7] = 1 odd,
so f(26) = 7 = floor(26/2) - 6.
"""
import itertools


def apfree(a):
    pos = {v: i for i, v in enumerate(a)}
    for i, x in enumerate(a):
        for z in a[i + 2:]:
            if (x + z) % 2 == 0 and i < pos.get((x + z) // 2, -1) < pos[z]:
                return False
    return True


def perms(K, ok_prefix, ok_full):
    a = []
    used = set()

    def rec():
        if len(a) == K:
            if ok_full(a):
                yield list(a)
            return
        for v in range(1, K + 1):
            if v in used:
                continue
            a.append(v)
            used.add(v)
            if apfree(a) and ok_prefix(a):
                yield from rec()
            a.pop()
            used.discard(v)

    return rec()


K = 13
sigma = next(perms(K, lambda a: all(v >= 7 for v in a[7:]), lambda a: True))
tau = next(perms(K, lambda a: a[0] == 1, lambda a: True))
a = [2 * r for r in sigma[:7]] + [1] + [2 * r for r in sigma[7:]] + [2 * r - 1 for r in tau[1:]]
assert sorted(a) == list(range(1, 27)) and apfree(a)
print(a)

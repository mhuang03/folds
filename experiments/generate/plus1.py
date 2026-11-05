"""The "+1" question: extending a valid N-sequence to a valid (N+1)-sequence.

Two insertion operations on a valid sequence a of [N]:
  top(a, p):    insert the new panel N+1 at position p (0..N)
  bottom(a, p): shift every panel up by one and insert panel 1 at position p
and the deletion of panel N (resp. 1) from a valid sequence of [N].

For each N prints:
  ext_top    fraction of valid N-seqs with at least one valid top insertion
  ext_any    ... with at least one valid top or bottom insertion
  pos        histogram of valid top-insertion positions (0 = first)
  del_ok     fraction of valid (N+1)-seqs whose deletion of N+1 is valid for [N]
  img        fraction of valid (N+1)-seqs obtained by a top insertion (= del_ok)
Usage: python3 plus1.py [Nmax]
"""
import sys
from collections import Counter

from brute import valid_seqs, is_valid


def top_ins(a, p, N):
    return a[:p] + (N + 1,) + a[p:]


def bot_ins(a, p, N):
    b = tuple(x + 1 for x in a)
    return b[:p] + (1,) + b[p:]


if __name__ == "__main__":
    Nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 9
    for N in range(1, Nmax + 1):
        V = valid_seqs(N)
        V1 = set(valid_seqs(N + 1))
        ext_top = ext_any = 0
        pos = Counter()
        npos = Counter()
        for a in V:
            ps = [p for p in range(N + 1) if top_ins(a, p, N) in V1]
            qs = [p for p in range(N + 1) if bot_ins(a, p, N) in V1]
            for p in ps:
                pos[p] += 1
            npos[len(ps)] += 1
            ext_top += bool(ps)
            ext_any += bool(ps or qs)
        dele = sum(1 for b in V1 if is_valid(tuple(x for x in b if x != N + 1), N))
        print(f"N={N}: a={len(V)} ext_top={ext_top/len(V):.3f} ext_any={ext_any/len(V):.3f} "
              f"del_ok={dele/len(V1):.3f}")
        print("   #valid top positions per seq:", dict(sorted(npos.items())))
        print("   positions:", [pos[p] for p in range(N + 1)])

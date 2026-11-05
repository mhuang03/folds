"""Insertion graph between minimum-descent words.  For every valid word on N (k = lg(N+1)
labels) and every insertion (position p in 1..N+1, label v), test validity on N+1 (when
lg(N+2) == k).  Report which (p, v) work, relative to N, and which N+1 words are reached."""
from words import words, valid_word
import sys
from collections import Counter
for N in range(int(sys.argv[1]), int(sys.argv[2]) + 1):
    k = (N + 1).bit_length() - 1
    if (N + 2).bit_length() - 1 != k: continue
    W = list(words(N, k)); W2 = set(tuple(w) for w in words(N + 1, k))
    reached = set(); moves = Counter(); src_ok = 0
    for w in W:
        any_ok = False
        for p in range(1, N + 2):
            for v in range(1, k + 1):
                w2 = w[:p] + [v] + w[p:]
                if valid_word(w2, N + 1):
                    reached.add(tuple(w2)); moves[(p - (N + 2) / 2, v)] += 1; any_ok = True
        src_ok += any_ok
    print(f'N={N}->{N+1}: words {len(W)} -> {len(W2)}; sources with an insertion {src_ok}; targets reached {len(reached)}')
    print('   moves (p - centre, label):', sorted(moves.items()))

def valid(S, m, N):
    """semi-symmetric step test: panel m, earlier set S."""
    r = min(m - 1, N - m)
    return sum((m - d) in S for d in range(1, r + 1)) == sum((m + d) in S for d in range(1, r + 1))

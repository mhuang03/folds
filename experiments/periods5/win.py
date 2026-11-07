"""win.py: max over beta != +-1 (units mod D) of the partial window products
prod_{i<L} 2^i / |2^i beta mod D|  for L = 1..s (exploration)."""
import numpy as np
for s in range(4, 19):
    D = 2 ** s - 1
    b = np.arange(2, D - 1, dtype=np.int64)
    b = b[np.gcd(b, D) == 1]
    L = np.zeros(len(b))
    best = []
    x = b.copy()
    for i in range(s):
        d = np.minimum(x % D, D - x % D)
        L += i * np.log(2) - np.log(d)
        j = np.argmax(L)
        best.append((round(float(np.exp(L[j])), 4), int(b[j])))
        x = (2 * x) % D
    print(s, best)

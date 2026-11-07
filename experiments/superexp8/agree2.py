# agree2.py: exceptional pairs for odd nu = 2w+1, q = 2m+1, odds first:
# sig_q(2i-1) = psi(sig_{m+1,w+1}(i)), psi(y) = 2y-1 (y <= w+1), 2y-2 (y > w+1);
# sig_q(2j) = chi(sig_{m,w}(j)), chi(z) = 2z (z <= w), 2z+1 (z > w).
from agree import exc
for m in range(3, 12):
    q = 2 * m + 1
    for w in range(0, m):
        psi = lambda y: 2 * y - 1 if y <= w + 1 else 2 * y - 2
        chi = lambda z: 2 * z if z <= w else 2 * z + 1
        print(f'm={m} w={w} psi:{exc(q, m + 1, psi)} chi:{exc(q, m, chi)}')

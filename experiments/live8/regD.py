"""regD.py N: coverage of the explicit direct-lemma region (Z, orientation 0, a = floor(u/2)):
  CA: (u - r) M (u + u' + 1) >= 2 (u + 1) (M u + 2 u u' + u - u' - 1)
  CB: (u M - r M - 2u + 2)(u' + 1) >= 2u (u'^2 + M)
(r = u mod 2, M = N + 2, u >= 4, u < u'), versus all wide mixed pairs; also the exact
sliding-window test with a = floor(u/2) (no slack) and with the best a."""
import sys

N = int(sys.argv[1])
M = N + 2


def exact(u, up, a):
    T = a * M
    S2 = T // u
    S1p = -(-(T + 1) // (u + 1))
    S1 = max(S1p, up, 2)
    S2 = min(S2, M // 2)
    if S1 > S2:
        return False
    return S2 * (up + 1) - S1 * up >= M


tot = cR = cE = cB = 0
for u in range(1, N):
    for up in range(u, N):
        if u + 2 * up > N - 1:
            break
        if (u + N + 1 - up) % 2 == 0:
            continue
        tot += 1
        r = u % 2
        if u >= 4 and up > u:
            CA = (u - r) * M * (u + up + 1) >= 2 * (u + 1) * (M * u + 2 * u * up + u - up - 1)
            CB = (u * M - r * M - 2 * u + 2) * (up + 1) >= 2 * u * (up * up + M)
            if CA and CB:
                cR += 1
                assert exact(u, up, (u - r) // 2), (u, up)
            if exact(u, up, (u - r) // 2):
                cE += 1
        if u >= 4 and up > u and any(exact(u, up, a) for a in range(2, u // 2 + 1)):
            cB += 1
print('N', N, 'wide mixed', tot, 'region CA&CB', cR, 'exact a=u/2', cE, 'exact best a', cB)

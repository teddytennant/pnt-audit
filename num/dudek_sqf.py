# Dudek (thesis arXiv:1611.07251, Theorem "erdos"; Dudek & Platt): every integer n >= 10 with n != 1 (mod 4) is p^2 + m with p prime, m squarefree.
import numpy as np
N = 200_000_000
sqf = np.ones(N + 1, bool); sqf[0] = False
for d in range(2, int(N**0.5) + 1):
    sqf[d*d::d*d] = False
left = np.ones(N + 1, bool); left[:10] = False; left[1::4] = False        # n >= 10, n != 1 mod 4, not yet represented
primes = [p for p in range(2, 2000) if all(p % q for q in range(2, int(p**0.5) + 1))]
used = 0
for p in primes:
    s = p * p
    if s >= N or not left.any(): break
    idx = np.nonzero(left[s+1:])[0] + s + 1          # n > p^2 still open
    ok = sqf[idx - s]; left[idx[ok]] = False; used = p
rem = np.nonzero(left)[0]
print(f'n <= {N}: unrepresented n (n >= 10, n != 1 mod 4): {rem[:20].tolist()} (count {len(rem)}); largest prime needed so far: {used}')

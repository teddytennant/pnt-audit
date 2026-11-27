# psi(x) - theta(x) only moves at proper prime powers, so bounds on it can be checked at every one of them up to 1e14.
import numpy as np, math
N = 10**14; r = 10**7
s = np.ones(r + 1, bool); s[:2] = False
for i in range(2, int(r**0.5) + 1):
    if s[i]: s[i*i::i] = False
pr = np.nonzero(s)[0].astype(object)
ev = []
for p in pr:
    q = p * p
    while q <= N:
        ev.append((q, math.log(p))); q *= p
ev.sort(); q = np.array([e[0] for e in ev], dtype=np.float64); d = np.cumsum(np.array([e[1] for e in ev]))
before = np.concatenate([[0.0], d[:-1]])
claims = [
 ('Dusart 2010 prop 3.2:  psi-theta < 1.00007 sqrt x + 1.78 x^(1/3), x>0', 0, lambda x: 1.00007*np.sqrt(x) + 1.78*np.cbrt(x), 'upper'),
 ('Platt-Trudgian (arXiv:1809.03134): psi-theta < (1+1.47e-7) sqrt x + 1.78 x^(1/3)', 0, lambda x: (1+1.47e-7)*np.sqrt(x) + 1.78*np.cbrt(x), 'upper'),
 ('Dusart 2010 prop 3.1:  0.9999 sqrt x < psi-theta, x>=121', 121, lambda x: 0.9999*np.sqrt(x), 'lower'),
]
for name, lo, f, kind in claims:
    if kind == 'upper':       # worst right after a jump
        m = q >= max(lo, 1); mg = f(q[m]) - d[m]; xs = q[m]
    else:                     # worst just before a jump: x -> q-, value before the jump
        m = q > lo; mg = before[m] - f(q[m]); xs = q[m]
    i = int(np.argmin(mg)); print(f"{'FAIL' if mg[i] < 0 else 'ok  '} {name}: worst {mg[i]:+.6g} at x={xs[i]:.0f}; {(mg < 0).sum()} failing prime powers <= 1e14")

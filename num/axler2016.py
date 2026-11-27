# Axler, "New bounds for the prime counting function", Integers 16 (2016), arXiv:1409.1780. From the LaTeX source.
import numpy as np, math, sys
from audit import run
ln = np.log
def S(x, c): L = ln(x); return x * sum(ck / L**(k + 1) for k, ck in enumerate(c))
def Dn(x, c): L = ln(x); return x / (L - sum(ck / L**k for k, ck in enumerate(c)))
UP = [1, 1, 2, 6.35, 24.35, 121.75, 730.5, 6801.4]; LO = [1, 1, 2, 5.65, 23.65, 118.25, 709.5, 4966.5]
DU = [1, 1, 3.35, 12.65, 71.7, 466.1275, 3489.8225]; DL = [1, 1, 2.65, 13.35, 70.3, 455.6275, 3404.4225]
C = [
 ('thm 1.1 pi < x/ln x + ... + 6801.4x/ln^8 x, x>1', 1, True, 1e300, lambda v: S(v['x'], UP) - v['pi']),
 ('thm 1.3 pi < x/(ln x - 1 - ... ), x>=e^3.804', math.exp(3.804), False, 1e300, lambda v: Dn(v['x'], DU) - v['pi']),
 ('thm 1.5 prime in (x, x(1+1.1817/ln^3 x)], x>=58837', 58837, False, 1e300, lambda v: np.where((v['isp'] == 1) & (v['tag'] == 'at'), v['x']*(1+1.1817/ln(v['x'])**3) - v['nextp'], np.nan)),
]
def window(lo, hi, pi_before, name, f):
    """pi(x) lower bounds near a large threshold: check at x=lo and as x -> p- for each prime p in (lo, hi]."""
    r = int(hi**0.5) + 1; s = np.ones(r + 1, bool); s[:2] = False
    for i in range(2, int(r**0.5) + 1):
        if s[i]: s[i*i::i] = False
    seg = np.ones(hi - lo + 1, bool)
    for p in np.nonzero(s)[0]:
        st = max(p * p, (lo + p - 1) // p * p); seg[st - lo::p] = False
    pr = np.nonzero(seg)[0] + lo
    pi_at = pi_before + np.arange(1, len(pr) + 1)                       # pi(p) for each prime p in [lo, hi]
    x = np.concatenate([[float(lo)], pr[pr > lo].astype(float)])
    pi_left = np.concatenate([[pi_before + (1 if seg[0] else 0)], pi_at[pr > lo] - 1])
    m = pi_left - f(x); i = int(np.argmin(m))
    print(f"{'FAIL' if m[i] < 0 else 'ok  '} {name:44s} worst {m[i]:+.6g} at x={x[i]:.12g} ({'endpoint' if i == 0 else 'left'}); {(m < 0).sum()} failing points in [{lo}, {hi}]")
if __name__ == '__main__':
    run(C, int(float(sys.argv[1])) if len(sys.argv) > 1 else 20_000_000)
    PI = {1332450000: int(sys.argv[2]), 1332479530: int(sys.argv[3])} if len(sys.argv) > 3 else {}
    if PI:
        window(1332450001, 1332450001 + 60_000_000, PI[1332450000], 'thm 1.2 pi > x/ln x + ... , x>=1332450001', lambda x: S(x, LO))
        window(1332479531, 1332479531 + 60_000_000, PI[1332479530], 'thm 1.4 pi > x/(ln x - 1 - ...), x>=1332479531', lambda x: Dn(x, DL))

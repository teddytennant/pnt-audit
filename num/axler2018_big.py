# Axler 2018, the three bounds whose thresholds sit near 1.9e10. pi and theta just below each threshold come from sieve.c.
import numpy as np, math
from axler2016 import window, S, Dn
window(19033744403, 19033744403 + 80_000_000, 841424975, 'thm 3.8  pi > x/(ln x-1-..-3428.7225/ln^6), x>=19033744403', lambda x: Dn(x, [1, 1, 2.85, 13.15, 70.7, 458.7275, 3428.7225]))
window(19027490297, 19027490297 + 80_000_000, 841160646, 'prop 3.11 pi > x/ln x+..+5008.5x/ln^8, x>=19027490297', lambda x: S(x, [1, 1, 2, 5.85, 23.85, 119.25, 715.5, 5008.5]))
# thm 2.4: theta(x) > x - 0.15 x/ln^3 x for x >= 19035709163
lo, hi, th0 = 19035709163, 19035709163 + 80_000_000, 19035493834.812828   # th0 = theta(lo - 1)
r = int(hi**0.5) + 1; s = np.ones(r + 1, bool); s[:2] = False
for i in range(2, int(r**0.5) + 1):
    if s[i]: s[i*i::i] = False
seg = np.ones(hi - lo + 1, bool)
for p in np.nonzero(s)[0]:
    st = max(p * p, (lo + p - 1) // p * p); seg[st - lo::p] = False
pr = (np.nonzero(seg)[0] + lo).astype(float)
th_at = th0 + np.cumsum(np.log(pr))
x = np.concatenate([[float(lo)], pr[pr > lo]]); th_left = np.concatenate([[th0 + (math.log(lo) if seg[0] else 0)], th_at[pr > lo] - np.log(pr[pr > lo])])
m = th_left - (x - 0.15 * x / np.log(x)**3); i = int(np.argmin(m))
print(f"{'FAIL' if m[i] < 0 else 'ok  '} thm 2.4  theta > x - 0.15x/ln^3 x, x>=19035709163    worst {m[i]:+.6g} at x={x[i]:.12g} ({'endpoint' if i == 0 else 'left'}); {(m < 0).sum()} failing points in the window")

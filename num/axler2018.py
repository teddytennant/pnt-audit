# Axler, "New estimates for some functions defined over primes", Integers 18 (2018), arXiv:1703.08032. From the LaTeX source.
import numpy as np, math, sys
from audit import run
ln = np.log; G = 0.5772156649015329; B = 0.2614972128476428; E = -1.3325822757332209
def S(x, c): L = ln(x); return x * sum(ck / L**(k + 1) for k, ck in enumerate(c))
def Dn(x, c): L = ln(x); return x / (L - sum(ck / L**k for k, ck in enumerate(c)))
gap = lambda f: (lambda v: np.where((v['isp'] == 1) & (v['tag'] == 'at'), v['x']*(1+f(v['x'])) - v['nextp'], np.nan))
C = [
 ('thm 2.4  theta < x + 0.15x/ln^3 x, x>1', 1, True, 1e300, lambda v: v['x'] + 0.15*v['x']/ln(v['x'])**3 - v['th']),
 ('prop 2.5 |theta-x| < 100x/ln^4 x, x>=70111', 70111, False, 1e300, lambda v: 100*v['x']/ln(v['x'])**4 - abs(v['th']-v['x'])),
 ('thm 3.2  pi < x/(ln x-1-1/ln x-3.15/..-4585/ln^6), x>=49', 49, False, 1e300, lambda v: Dn(v['x'], [1, 1, 3.15, 12.85, 71.3, 463.2275, 4585]) - v['pi']),
 ('prop 3.5 pi < x/(ln x-1-1/ln x-3/ln^2-113/ln^3), x>=41', 41, False, 1e300, lambda v: Dn(v['x'], [1, 1, 3, 113]) - v['pi']),
 ('prop 3.6 pi < x/ln x+..+6601x/ln^8 x, x>1', 1, True, 1e300, lambda v: S(v['x'], [1, 1, 2, 6.15, 24.15, 120.75, 724.5, 6601]) - v['pi']),
 ('prop 3.10 pi > x/(ln x-1-1/ln x-3/ln^2+87/ln^3), x>=19423', 19423, False, 1e300, lambda v: v['pi'] - Dn(v['x'], [1, 1, 3, -87])),
 ('thm 4.1  prime in (x, x(1+0.087/ln^3 x)], x>=6034256', 6034256, False, 1e300, gap(lambda x: 0.087/ln(x)**3)),
 ('thm 4.1  prime in (x, x(1+198.2/ln^4 x)], x>1', 1, True, 1e300, gap(lambda x: 198.2/ln(x)**4)),
 ('prop 5.1 sum 1/p lower, x>1', 1, True, 1e300, lambda v: v['S1'] - ln(ln(v['x'])) - B + 1/(20*ln(v['x'])**3) + 3/(16*ln(v['x'])**4)),
 ('prop 5.1 sum 1/p upper, x>=46909074', 46909074, False, 1e300, lambda v: 1/(20*ln(v['x'])**3) + 3/(16*ln(v['x'])**4) - (v['S1'] - ln(ln(v['x'])) - B)),
 ('prop 5.4 sum ln p/p lower, x>1', 1, True, 1e300, lambda v: v['S2'] - ln(v['x']) - E + 3/(40*ln(v['x'])**2) + 3/(20*ln(v['x'])**3)),
 ('prop 5.4 sum ln p/p upper, x>=30972320', 30972320, False, 1e300, lambda v: 3/(40*ln(v['x'])**2) + 3/(20*ln(v['x'])**3) - (v['S2'] - ln(v['x']) - E)),
 ('prop 6.1 prod(1-1/p) lower, x>=46909038', 46909038, False, 1e300, lambda v: np.exp(v['lP']) - math.exp(-G)/ln(v['x'])*(1 - 1/(20*ln(v['x'])**3) - 3/(16*ln(v['x'])**4))),
 ('prop 6.1 prod(1-1/p) < e^-g/ln x (1+0.07/ln^3 x), x>1', 1, True, 1e300, lambda v: math.exp(-G)/ln(v['x'])*(1 + 0.07/ln(v['x'])**3) - np.exp(v['lP'])),
]
if __name__ == '__main__': run(C, int(float(sys.argv[1])) if len(sys.argv) > 1 else 100_000_000)

# Dusart, "Estimates of some functions over primes without R.H.", arXiv:1002.0442. Statements copied from the LaTeX source.
import numpy as np, math, sys
from audit import run
ln = np.log; G = 0.5772156649015329; B = 0.2614972128476428; E = -1.3325822757332209
prime = lambda v: np.where((v['isp'] == 1) & (v['tag'] == 'at'), 1.0, np.nan)   # claims indexed by k: only at x = p_k
def l2(k): return ln(ln(k))
def eta(k, e): return lambda v: e * v['x'] / ln(v['x'])**k - abs(v['th'] - v['x'])
C = [
 ('prop 3.1  0.9999 sqrt x < psi-theta, x>=121', 121, False, 1e300, lambda v: (v['ps']-v['th']) - 0.9999*np.sqrt(v['x'])),
 ('prop 3.2  psi-theta < 1.00007 sqrt x + 1.78 x^(1/3)', 0, True, 1e300, lambda v: 1.00007*np.sqrt(v['x']) + 1.78*np.cbrt(v['x']) - (v['ps']-v['th'])),
 ('prop 5.1  theta(x)-x < x/36260', 0, True, 1e300, lambda v: v['x']/36260 - (v['th']-v['x'])),
 ('thm 5.2   k=0 eta=1 x>=1', 1, False, 1e300, eta(0, 1)),
 ('thm 5.2   k=1 eta=1.2323 x>=2', 2, False, 1e300, eta(1, 1.2323)),
 ('thm 5.2   k=2 eta=3.965 x>=2', 2, False, 1e300, eta(2, 3.965)),
 ('thm 5.2   k=2 eta=0.2 x>=3594641', 3594641, False, 1e300, eta(2, 0.2)),
 ('thm 5.2   k=3 eta=20.83 x>=2', 2, False, 1e300, eta(3, 20.83)),
 ('thm 5.2   k=3 eta=10 x>=32321', 32321, False, 1e300, eta(3, 10)),
 ('thm 5.2   k=4 eta=1300 x>=2', 2, False, 1e300, eta(4, 1300)),
 ('prop 6.2  theta(p_k) upper, k>=781', 2, False, 1e300, lambda v: prime(v)*np.where(v['pi'] >= 781, v['pi']*(ln(v['pi'])+l2(v['pi'])-1+(l2(v['pi'])-2)/ln(v['pi'])-0.782/ln(v['pi'])**2) - v['th'], np.nan)),
 ('lem 6.4   p_k upper (1.95), k>=178974', 2, False, 1e300, lambda v: prime(v)*np.where(v['pi'] >= 178974, v['pi']*(ln(v['pi'])+l2(v['pi'])-1+(l2(v['pi'])-1.95)/ln(v['pi'])) - v['x'], np.nan)),
 ('prop 6.6  p_k upper (2), k>=688383', 2, False, 1e300, lambda v: prime(v)*np.where(v['pi'] >= 688383, v['pi']*(ln(v['pi'])+l2(v['pi'])-1+(l2(v['pi'])-2)/ln(v['pi'])) - v['x'], np.nan)),
 ('prop 6.7  p_k lower (2.1), k>=3', 2, False, 1e300, lambda v: prime(v)*np.where(v['pi'] >= 3, v['x'] - v['pi']*(ln(v['pi'])+l2(v['pi'])-1+(l2(v['pi'])-2.1)/ln(v['pi'])), np.nan)),
 ('prop 6.8  prime in (x, x(1+1/(25 ln^2 x))], x>=396738', 396738, False, 1e300, lambda v: np.where((v['isp'] == 1) & (v['tag'] == 'at'), v['x']*(1+1/(25*ln(v['x'])**2)) - v['nextp'], np.nan)),
 ('thm 6.9   x/ln x (1+1/ln x) <= pi, x>=599', 599, False, 1e300, lambda v: v['pi'] - v['x']/ln(v['x'])*(1+1/ln(v['x']))),
 ('thm 6.9   pi <= x/ln x (1+1.2762/ln x), x>1', 1, True, 1e300, lambda v: v['x']/ln(v['x'])*(1+1.2762/ln(v['x'])) - v['pi']),
 ('thm 6.9   x/(ln x -1) <= pi, x>=5393', 5393, False, 1e300, lambda v: v['pi'] - v['x']/(ln(v['x'])-1)),
 ('thm 6.9   pi <= x/(ln x -1.1), x>=60184', 60184, False, 1e300, lambda v: v['x']/(ln(v['x'])-1.1) - v['pi']),
 ('thm 6.9   x/ln x (1+1/ln x+2/ln^2 x) <= pi, x>=88783', 88783, False, 1e300, lambda v: v['pi'] - v['x']/ln(v['x'])*(1+1/ln(v['x'])+2/ln(v['x'])**2)),
 ('thm 6.10  sum 1/p lower, x>1', 1, True, 1e300, lambda v: v['S1'] - l2(v['x']) - B + (1/(10*ln(v['x'])**2) + 4/(15*ln(v['x'])**3))),
 ('thm 6.10  sum 1/p upper, x>=10372', 10372, False, 1e300, lambda v: (1/(10*ln(v['x'])**2) + 4/(15*ln(v['x'])**3)) - (v['S1'] - l2(v['x']) - B)),
 ('thm 6.11  sum ln p/p lower, x>1', 1, True, 1e300, lambda v: v['S2'] - ln(v['x']) - E + (0.2/ln(v['x']) + 0.2/ln(v['x'])**2)),
 ('thm 6.11  sum ln p/p upper, x>=2974', 2974, False, 1e300, lambda v: (0.2/ln(v['x']) + 0.2/ln(v['x'])**2) - (v['S2'] - ln(v['x']) - E)),
 ('thm 6.12  prod(1-1/p) upper, x>1', 1, True, 1e300, lambda v: math.exp(-G)/ln(v['x'])*(1+0.2/ln(v['x'])**2) - np.exp(v['lP'])),
 ('thm 6.12  prod(1-1/p) lower, x>=2973', 2973, False, 1e300, lambda v: np.exp(v['lP']) - math.exp(-G)/ln(v['x'])*(1-0.2/ln(v['x'])**2)),
 ('thm 6.12  prod p/(p-1) lower, x>1', 1, True, 1e300, lambda v: np.exp(-v['lP']) - math.exp(G)*ln(v['x'])*(1-0.2/ln(v['x'])**2)),
 ('thm 6.12  prod p/(p-1) upper, x>=2973', 2973, False, 1e300, lambda v: math.exp(G)*ln(v['x'])*(1+0.2/ln(v['x'])**2) - np.exp(-v['lP'])),
]
if __name__ == '__main__': run(C, int(float(sys.argv[1])) if len(sys.argv) > 1 else 20_000_000)

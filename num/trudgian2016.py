# Trudgian, "Updating the error term in the prime number theorem", Ramanujan J. 39 (2016), arXiv:1401.2689. From the LaTeX source.
import numpy as np, math, sys
from audit import run, li
ln = np.log
def e0(x, R=6.455):
    X = np.sqrt(ln(x) / R); return math.sqrt(8 / (17 * math.pi)) * np.sqrt(X) * np.exp(-X)
C = [
 ('thm 1  |theta-x| <= x eps0(x), x>=149', 149, False, 1e300, lambda v: v['x']*e0(v['x']) - abs(v['th']-v['x'])),
 ('thm 1  |psi-x| <= x eps0(x), x>=23', 23, False, 1e300, lambda v: v['x']*e0(v['x']) - abs(v['ps']-v['x'])),
 ('thm 2  |pi-li| <= 0.2795 x/(ln x)^.75 exp(-sqrt(ln x/6.455)), x>=229', 229, False, 1e300,
    lambda v: 0.2795*v['x']/ln(v['x'])**0.75*np.exp(-np.sqrt(ln(v['x'])/6.455)) - abs(v['pi']-li(v['x']))),
 ('cor 2  prime in [x, x(1+1/(111 ln^2 x))], x>=2898239', 2898239, False, 1e300,
    lambda v: np.where((v['isp'] == 1) & (v['tag'] == 'at'), v['x']*(1+1/(111*ln(v['x'])**2)) - v['nextp'], np.nan)),
]
if __name__ == '__main__': run(C, int(float(sys.argv[1])) if len(sys.argv) > 1 else 20_000_000)

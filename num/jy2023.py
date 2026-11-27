# Johnston & Yang, "Some explicit estimates for the error term in the prime number theorem", arXiv:2204.01980. From the LaTeX source.
import numpy as np, sys
from audit import run, li
ln = np.log
vk = lambda c, b, x: c*x*ln(x)**b*np.exp(-0.1853*ln(x)**0.6*ln(ln(x))**-0.2)
C = [
 ('thm 1.1 |psi-x| <= 9.39x(ln x)^1.515 exp(-0.8274 sqrt ln x), x>=2', 2, False, 1e300, lambda v: 9.39*v['x']*ln(v['x'])**1.515*np.exp(-0.8274*np.sqrt(ln(v['x']))) - abs(v['ps']-v['x'])),
 ('cor 1.3 |pi-li| <= 9.59x(ln x)^0.515 exp(-0.8274 sqrt ln x), x>=2', 2, False, 1e300, lambda v: 9.59*v['x']*ln(v['x'])**0.515*np.exp(-0.8274*np.sqrt(ln(v['x']))) - abs(v['pi']-li(v['x']))),
 ('thm 1.4 psi VK bound, x>=23', 23, False, 1e300, lambda v: vk(0.026, 1.801, v['x']) - abs(v['ps']-v['x'])),
 ('thm 1.4 theta VK bound, x>=23', 23, False, 1e300, lambda v: vk(0.027, 1.801, v['x']) - abs(v['th']-v['x'])),
 ('thm 1.4 pi-li VK bound, x>=23', 23, False, 1e300, lambda v: vk(0.028, 0.801, v['x']) - abs(v['pi']-li(v['x']))),
]
if __name__ == '__main__': run(C, int(float(sys.argv[1])) if len(sys.argv) > 1 else 20_000_000)

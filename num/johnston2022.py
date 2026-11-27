# Johnston, "Improving bounds on prime counting functions by partial verification of the Riemann hypothesis", arXiv:2109.02249.
# Theorem 1.1 (label mainthm) from the LaTeX source. Its hypothesis holds for every x here with T = 3e12.
import numpy as np, math, sys
from audit import run, li
ln = np.log; b = lambda x, k: np.sqrt(x)*ln(x)**k/(8*math.pi)
C = [
 ('thm 1.1 |psi-x| < sqrt x ln^2 x/(8pi), x>=59', 59, False, 1e300, lambda v: b(v['x'], 2) - abs(v['ps']-v['x'])),
 ('thm 1.1 |theta-x| < sqrt x ln^2 x/(8pi), x>=599', 599, False, 1e300, lambda v: b(v['x'], 2) - abs(v['th']-v['x'])),
 ('thm 1.1 |Pi-li| < sqrt x ln x/(8pi), x>=59', 59, False, 1e300, lambda v: b(v['x'], 1) - abs(v['Pi']-li(v['x']))),
 ('thm 1.1 |pi-li| < sqrt x ln x/(8pi), x>=2657', 2657, False, 1e300, lambda v: b(v['x'], 1) - abs(v['pi']-li(v['x']))),
]
if __name__ == '__main__': run(C, int(float(sys.argv[1])) if len(sys.argv) > 1 else 20_000_000)

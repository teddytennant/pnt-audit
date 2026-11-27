# Would the arXiv v1 form of Buthe (1.6) do as the corrected statement?  x - theta(x) <= 1.94 sqrt x for 1427 < x.
# And the journal's constant with the threshold moved: 1.95 sqrt x for 1427 <= x.
import numpy as np, sys
from audit import run
C = [('arXiv v1: x-theta <= 1.94 sqrt x, x>1427', 1427, True, 1e300, lambda v: 1.94*np.sqrt(v['x']) - (v['x']-v['th'])),
     ('journal constant, moved: 1.95 sqrt x, x>=1427', 1427, False, 1e300, lambda v: 1.95*np.sqrt(v['x']) - (v['x']-v['th'])),
     ('(7.1) moved: |pi*-li| <= sqrt x ln x/(8pi), x>=97', 97, False, 1e300, lambda v: np.sqrt(v['x'])*np.log(v['x'])/(8*np.pi) - abs(v['Pi']-__import__('audit').li(v['x'])))]
run(C, int(float(sys.argv[1])) if len(sys.argv) > 1 else 20_000_000)

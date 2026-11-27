# Lee & Nosal, "Sharper bounds for the error in the prime number theorem assuming the Riemann Hypothesis", arXiv:2312.05628.
# Stated under RH. For x in this range the statements are plain numerical claims, true or false either way.
import numpy as np, math, sys
from audit import run
ln = np.log; G = 0.5772156649015329; B = 0.2614972128476428; E = -1.3325822757332209; pi8 = 8*math.pi
C = [
 ('thm 1.1 |psi-x| <= sqrt x ln x (ln x/8pi - (1/2pi+1.465/ln x) lnln x + 1.2325), x>=11', 11, False, 1e300,
    lambda v: np.sqrt(v['x'])*ln(v['x'])*(ln(v['x'])/pi8 - (1/(2*math.pi) + 1.465/ln(v['x']))*ln(ln(v['x'])) + 1.2325) - abs(v['ps']-v['x'])),
 ('thm 1.2 |psi-x| <= sqrt x ln x (ln x - lnln x)/8pi, x>=101', 101, False, 1e300, lambda v: np.sqrt(v['x'])*ln(v['x'])*(ln(v['x'])-ln(ln(v['x'])))/pi8 - abs(v['ps']-v['x'])),
 ('thm 1.2 |theta-x| <= sqrt x ln x (ln x - lnln x)/8pi, x>=2657', 2657, False, 1e300, lambda v: np.sqrt(v['x'])*ln(v['x'])*(ln(v['x'])-ln(ln(v['x'])))/pi8 - abs(v['th']-v['x'])),
 ('cor 1.3 |sum ln p/p - ln x - E| <= 3 ln^2 x/(8pi sqrt x), x>=43.1', 43.1, False, 1e300, lambda v: 3*ln(v['x'])**2/(pi8*np.sqrt(v['x'])) - abs(v['S2']-ln(v['x'])-E)),
 ('cor 1.3 |sum 1/p - lnln x - B| <= 3 ln x/(8pi sqrt x), x>=24.4', 24.4, False, 1e300, lambda v: 3*ln(v['x'])/(pi8*np.sqrt(v['x'])) - abs(v['S1']-ln(ln(v['x']))-B)),
 ('cor 1.3 |e^g ln x prod(1-1/p) - 1| <= 3 ln x/(8pi sqrt x), x>=23.8', 23.8, False, 1e300, lambda v: 3*ln(v['x'])/(pi8*np.sqrt(v['x'])) - abs(math.exp(G)*ln(v['x'])*np.exp(v['lP'])-1)),
 ('cor 1.3 |e^-g/ln x prod(1-1/p)^-1 - 1| <= 3 ln x/(8pi sqrt x), x>=24.2', 24.2, False, 1e300, lambda v: 3*ln(v['x'])/(pi8*np.sqrt(v['x'])) - abs(math.exp(-G)/ln(v['x'])*np.exp(-v['lP'])-1)),
]
if __name__ == '__main__': run(C, int(float(sys.argv[1])) if len(sys.argv) > 1 else 20_000_000)

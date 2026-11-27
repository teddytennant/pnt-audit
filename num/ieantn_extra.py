# Two more IEANTN nodes: Dusart2018.v1.proposition_5_4 and BKLNW.v1/v2.corollary_5_1, as stated in the nodes.
import numpy as np, math, sys
from audit import run, build
ln = np.log
C = [('Dusart2018 prop 5.4 prime in (x, x(1+1/ln^3 x)], x>=89693', 89693, False, 1e300,
      lambda v: np.where((v['isp'] == 1) & (v['tag'] == 'at'), v['x']*(1+1/ln(v['x'])**3) - v['nextp'], np.nan))]
N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 20_000_000
run(C, N)
# x in [89693, next prime): no prime event at the endpoint, so check it directly
def isp(n): return n > 1 and all(n % d for d in range(2, int(n**0.5) + 1))
x = 89693; p = x + 1
while not isp(p): p += 1
print(f'     endpoint x=89693 (prime: {isp(x)}): next prime {p}, upper end {x*(1+1/math.log(x)**3):.4f}, holds={p <= x*(1+1/math.log(x)**3)}')
# BKLNW Corollary 5.1: for 7 <= b <= 38 ln 10 and x >= e^b,  psi - theta < (1+a) sqrt x + a2(b) x^(1/3)
A = 1.93378e-8
def f(x): return sum(x**(1/k - 1/3) for k in range(3, int(math.floor(math.log(x)/math.log(2) + 1e-12)) + 1))
def a2(b): return (1 + A) * max(f(math.exp(b)), f(2.0 ** (math.floor(b/math.log(2)) + 1)))
at, left = build(N); m = (at['x'] >= math.exp(7)) & (at['isp'] == 0)        # psi - theta only jumps at proper prime powers
xs = at['x'][m]; d = (at['ps'] - at['th'])[m]
bs = sorted(set([7.0] + [k*math.log(2) - 1e-9 for k in range(11, 60)] + [k*math.log(2) for k in range(11, 60)]))
worst = (1e9, None, None)
for xv, dv in zip(xs, d):
    L = math.log(xv)
    for b in [bb for bb in bs if bb <= L] + [L]:
        if b > 38*math.log(10): continue
        mg = (1 + A)*math.sqrt(xv) + a2(b)*xv**(1/3) - dv
        if mg < worst[0]: worst = (mg, xv, b)
print(f"{'FAIL' if worst[0] < 0 else 'ok  '} BKLNW cor 5.1 worst margin {worst[0]:+.6g} at x={worst[1]:.10g}, b={worst[2]:.6f}")

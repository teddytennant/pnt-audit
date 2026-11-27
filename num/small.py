# Exact check of every finite-range claim at each prime power q <= N, at x=q and at the left limit x->q-.
import numpy as np, math, sys
N = int(float(sys.argv[1])) if len(sys.argv) > 1 else 20_000_000
s = np.ones(N + 1, bool); s[:2] = False
for i in range(2, int(N**0.5) + 1):
    if s[i]: s[i*i::i] = False
pr = np.nonzero(s)[0]
q = [pr.astype(np.float64)]; dth = [np.log(pr)]; dps = [np.log(pr)]; dpi = [np.ones(len(pr))]; dPi = [np.ones(len(pr))]
k = 2
while 2**k <= N:
    pk = pr[pr <= int(round(N ** (1 / k))) + 1].astype(object) ** k
    pk = np.array([v for v in pk if v <= N], dtype=np.float64); base = np.round(pk ** (1 / k))
    q.append(pk); dth.append(np.zeros(len(pk))); dps.append(np.log(base)); dpi.append(np.zeros(len(pk))); dPi.append(np.full(len(pk), 1 / k)); k += 1
q = np.concatenate(q); o = np.argsort(q, kind='stable'); q = q[o]
cs = lambda a: np.cumsum(np.concatenate(a)[o])
th1, ps1, pi1, Pi1 = cs(dth), cs(dps), cs(dpi), cs(dPi)            # values at x = q
pre = lambda a: np.concatenate([[0.0], a[:-1]])
th0, ps0, pi0, Pi0 = pre(th1), pre(ps1), pre(pi1), pre(Pi1)        # values as x -> q-
def li(x):
    L = np.log(x); t = np.ones_like(L); acc = np.zeros_like(L)
    for n in range(1, 140): t = t * L / n; acc += t / n
    return 0.5772156649015329 + np.log(L) + acc
LI2 = 1.0451637801174927
R = 9.645908801
def eps0(x):
    X = np.sqrt(np.log(x) / R); return math.sqrt(8 / (17 * math.pi)) * np.sqrt(X) * np.exp(-X)
adm = lambda A, B, C, R_, x: A * (np.log(x) / R_) ** B * np.exp(-C * np.sqrt(np.log(x) / R_))
sq, lg = np.sqrt, np.log
# name, lo, lo_strict, hi, margin(x, th, ps, pi, Pi) which the claim says is > 0 (or >= 0)
C = [
 ('Buthe.theorem_2_psi', 11, True, 1e19, lambda x,th,ps,pi,Pi: 0.94*sq(x) - abs(x-ps)),
 ('Buthe.theorem_2_theta', 1423, False, 1e19, lambda x,th,ps,pi,Pi: 1.95*sq(x) - (x-th)),
 ('Buthe.theorem_2_theta_lower', 1, False, 1e19, lambda x,th,ps,pi,Pi: (x-th) - 0.05*sq(x)),
 ('Buthe.theorem_2_li_minus_riemann_pi', 2, False, 1e19, lambda x,th,ps,pi,Pi: sq(x)/lg(x) - abs(li(x)-Pi)),
 ('Buthe.theorem_2_li_minus_pi', 2, False, 1e19, lambda x,th,ps,pi,Pi: sq(x)/lg(x)*(1.95+3.9/lg(x)+19.5/lg(x)**2) - (li(x)-pi)),
 ('Buthe.theorem_2_li_gt_pi', 2, False, 1e19, lambda x,th,ps,pi,Pi: li(x)-pi),
 ('ButheNumerics.eq_6_2.lower', 100, False, 5e10, lambda x,th,ps,pi,Pi: (x-ps)/sq(x) + 0.8),
 ('ButheNumerics.eq_6_2.upper', 100, False, 5e10, lambda x,th,ps,pi,Pi: 0.81 - (x-ps)/sq(x)),
 ('Buthe2016.theorem_2_psi', 59, True, 1e25, lambda x,th,ps,pi,Pi: sq(x)*lg(x)**2/(8*math.pi) - abs(ps-x)),
 ('Buthe2016.theorem_2_theta', 599, True, 1e25, lambda x,th,ps,pi,Pi: sq(x)*lg(x)**2/(8*math.pi) - abs(th-x)),
 ('Buthe2016.theorem_2_li_minus_riemann_pi', 59, True, 1e25, lambda x,th,ps,pi,Pi: sq(x)*lg(x)/(8*math.pi) - abs(Pi-li(x))),
 ('Buthe2016.theorem_2_li_minus_pi', 2657, True, 1e25, lambda x,th,ps,pi,Pi: sq(x)*lg(x)/(8*math.pi) - abs(pi-li(x))),
 ('Schoenfeld1976.psi_theorem_11', 17, False, 1e300, lambda x,th,ps,pi,Pi: x*eps0(x) - abs(ps-x)),
 ('Schoenfeld1976.theta_theorem_11', 101, False, 1e300, lambda x,th,ps,pi,Pi: x*eps0(x) - abs(th-x)),
 ('Schoenfeld1976.psi_upper_theorem_11', 1, False, 1e300, lambda x,th,ps,pi,Pi: x*eps0(x) - (ps-x)),
 ('Schoenfeld1976.psi_log_5_5a', 161971, False, 1e300, lambda x,th,ps,pi,Pi: 0.0220646*x/lg(x) - abs(ps-x)),
 ('Schoenfeld1976.psi_log_lower_5_5b', 89909, False, 1e300, lambda x,th,ps,pi,Pi: (ps-x) + 0.0220646*x/lg(x)),
 ('Schoenfeld1976.theta_log_5_6', 758711, False, 1e300, lambda x,th,ps,pi,Pi: 0.0239922*x/lg(x) - abs(th-x)),
 ('Schoenfeld1976.theta_log_upper_5_6a', 1, True, 1e300, lambda x,th,ps,pi,Pi: 0.0201384*x/lg(x) - (th-x)),
 ('FKS.psi_bound_all_x', 2, True, 1e300, lambda x,th,ps,pi,Pi: 9.22022*lg(x)**1.5*np.exp(-0.8476836*sq(lg(x))) - abs(ps-x)/x),
 ('FKS2Numerics.table6_row2_floor', math.e, False, math.exp(6), lambda x,th,ps,pi,Pi: adm(0.826,0.25,1,5.5666305,x) - abs(pi-(li(x)-LI2))/(x/lg(x))),
 ('FKS2Numerics.corollary_22_mid_range', 2, False, 1e300, lambda x,th,ps,pi,Pi: adm(9.2211,1.5,0.84768363,1,x) - abs(pi-(li(x)-LI2))/(x/lg(x))),
 ('FKS2Numerics.corollary_23_mid_range', math.exp(6), False, 1e300, lambda x,th,ps,pi,Pi: adm(0.826,0.25,1,5.5666305,x) - abs(pi-(li(x)-LI2))/(x/lg(x))),
 ('FKS2.corollary_26', 2, False, 1e300, lambda x,th,ps,pi,Pi: 0.4298 - abs(pi-(li(x)-LI2))/(x/lg(x))),
]
for name, lo, strict, hi, f in C:
    m = (q > lo) & (q <= hi)
    with np.errstate(all='ignore'):
        a = f(q[m], th1[m], ps1[m], pi1[m], Pi1[m]); b = f(q[m], th0[m], ps0[m], pi0[m], Pi0[m])
    xs = q[m]; best = []
    for tag, arr in (('at', a), ('left', b)):
        i = int(np.nanargmin(arr)); best.append((arr[i], xs[i], tag))
    # the lower endpoint itself, when it is in the domain and not a jump point
    if not strict and lo >= 2:
        j = np.searchsorted(q, lo, side='right') - 1
        v = float(f(np.array([float(lo)]), th1[j:j+1], ps1[j:j+1], pi1[j:j+1], Pi1[j:j+1])[0]); best.append((v, lo, 'endpoint'))
    w = min(best)
    nviol = int((a < 0).sum() + (b < 0).sum())
    print(f"{'FAIL' if w[0] < 0 else 'ok  '} {name:45s} worst margin {w[0]:+.6g} at x={w[1]:.10g} ({w[2]}), {nviol} violating points up to {N:g}")

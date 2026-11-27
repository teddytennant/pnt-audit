# Check published explicit bounds at every prime power q <= N: at x = q, and as x -> q from the left.
# A claim is (name, lo, lo_strict, hi, margin) where margin(v) >= 0 is what the paper asserts on its domain.
import numpy as np, math, sys
def build(N):
    s = np.ones(N + 1, bool); s[:2] = False
    for i in range(2, int(N**0.5) + 1):
        if s[i]: s[i*i::i] = False
    pr = np.nonzero(s)[0]; lp = np.log(pr); z = np.zeros
    cols = {'q': [pr.astype(float)], 'th': [lp], 'ps': [lp], 'ps3': [z(len(pr))], 'pi': [np.ones(len(pr))], 'Pi': [np.ones(len(pr))],
            'S1': [1.0 / pr], 'S2': [lp / pr], 'lP': [np.log1p(-1.0 / pr)], 'isp': [np.ones(len(pr))]}
    k = 2
    while 2**k <= N:
        b = pr[pr.astype(object) ** k <= N]; n = len(b)
        cols['q'].append((b.astype(object) ** k).astype(float)); cols['th'].append(z(n)); cols['ps'].append(np.log(b))
        cols['ps3'].append(np.log(b) if k >= 3 else z(n)); cols['pi'].append(z(n)); cols['Pi'].append(np.full(n, 1 / k))
        for c in ('S1', 'S2', 'lP', 'isp'): cols[c].append(z(n))
        k += 1
    q = np.concatenate(cols['q']); o = np.argsort(q, kind='stable')
    at = {'x': q[o], 'isp': np.concatenate(cols['isp'])[o]}; left = {'x': q[o], 'isp': at['isp']}
    for c in ('th', 'ps', 'ps3', 'pi', 'Pi', 'S1', 'S2', 'lP'):
        a = np.cumsum(np.concatenate(cols[c])[o]); at[c] = a; left[c] = np.concatenate([[0.0], a[:-1]])
    nxt = np.concatenate([pr[1:], [np.nan]]).astype(float)        # next prime after each prime
    npr = np.full(len(q), np.nan); npr[np.concatenate(cols['isp'])[o] == 1] = nxt; at['nextp'] = npr; left['nextp'] = npr
    return at, left
def li(x):
    L = np.log(x); t = np.ones_like(L); acc = np.zeros_like(L)
    for n in range(1, 140): t = t * L / n; acc += t / n
    return 0.5772156649015329 + np.log(L) + acc
def run(claims, N):
    at, left = build(N); x = at['x']; out = []
    for name, lo, strict, hi, f in claims:
        m = (x > lo) & (x <= hi) if strict else (x >= lo) & (x <= hi)
        ml = (x > lo) & (x <= hi)                                  # left limits need points of the domain below q
        res = []
        with np.errstate(all='ignore'):
            for tag, d, mm in (('at', at, m), ('left', left, ml)):
                v = {k: a[mm] for k, a in d.items()}; v['tag'] = tag
                if not len(v['x']): continue
                a = np.asarray(f(v), float); ok = ~np.isnan(a)
                if ok.any(): i = int(np.nanargmin(a)); res.append((float(a[i]), float(v['x'][i]), tag, int((a[ok] < 0).sum())))
            if not strict and lo > 2:                               # the lower endpoint itself
                j = int(np.searchsorted(x, lo, side='right')) - 1
                v = {k: a[j:j+1].copy() for k, a in at.items()}; v['x'] = np.array([float(lo)]); v['tag'] = 'endpoint'; v['isp'] = np.array([0.0])
                a = np.asarray(f(v), float)
                if not np.isnan(a[0]): res.append((float(a[0]), float(lo), 'endpoint', int(a[0] < 0)))
        w = min(res); nv = sum(r[3] for r in res)
        print(f"{'FAIL' if w[0] < 0 else 'ok  '} {name:44s} worst {w[0]:+.6g} at x={w[1]:.12g} ({w[2]}); {nv} failing points <= {N:g}", flush=True)
        out.append((name, w, nv))
    return out

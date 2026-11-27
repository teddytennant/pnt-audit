# Independent check of OEIS A105720 at n = 111008771: sum of the primes p_n .. p_2n, by a numpy segmented sieve.
import numpy as np, math
n = 111008771; lo_i, hi_i = n, 2 * n                      # 1-based prime indices, inclusive
LIM = 5_000_000_000; r = int(LIM**0.5) + 1
s = np.ones(r + 1, bool); s[:2] = False
for i in range(2, int(r**0.5) + 1):
    if s[i]: s[i*i::i] = False
small = np.nonzero(s)[0]
count = 0; total = 0; first = last = None; SEG = 1 << 25
for lo in range(2, LIM, SEG):
    hi = min(lo + SEG, LIM); seg = np.ones(hi - lo, bool)
    for p in small:
        if p * p >= hi: break
        st = max(p * p, (lo + p - 1) // p * p); seg[st - lo::p] = False
    pr = np.nonzero(seg)[0].astype(np.int64) + lo
    a, b = count + 1, count + len(pr)                     # indices covered by this segment
    if b >= lo_i and a <= hi_i:
        sel = pr[max(lo_i - a, 0): hi_i - a + 1]
        total += int(sel.sum(dtype=object)) if False else sum(int(x) for x in (sel[:0])) + int(np.sum(sel.astype(np.uint64) >> np.uint64(0), dtype=np.uint64)) if len(sel) < 1 else int(sel.astype(object).sum()) if len(sel) < 1000 else sum(int(c.sum()) for c in np.array_split(sel, 64))
        if first is None and len(sel): first = int(sel[0])
        if len(sel): last = int(sel[-1])
    count = b
    if count > hi_i: break
rt = math.isqrt(total)
print(f'p_n = {first}, p_2n = {last}, terms = {hi_i - lo_i + 1}')
print(f'sum = {total}\nisqrt = {rt}, square: {rt * rt == total}')

# 50-digit confirmation of the two failures, with no floating point.
from decimal import Decimal as D, getcontext
getcontext().prec = 60
def primes(n): return [p for p in range(2, n + 1) if all(p % d for d in range(2, int(p**0.5) + 1))]
PI = D('3.14159265358979323846264338327950288419716939937510582097494')
GAMMA = D('0.577215664901532860606512090082402431042159335939923598805767')
def li(x):                     # li(x) = gamma + ln ln x + sum (ln x)^n / (n * n!)
    L = x.ln(); t = D(1); acc = D(0)
    for n in range(1, 400): t = t * L / n; acc += t / n
    return GAMMA + L.ln() + acc
print('A. Buthe 2018, Theorem 2 (1.6):  x - theta(x) <= 1.95 sqrt(x)  for 1423 <= x <= 1e19')
for x in (D(1423), D(1426), D('1426.5'), D('1426.9'), D('1426.999999')):
    th = sum(D(p).ln() for p in primes(int(x)))
    print(f'  x={x}: theta={th:.10f}  x-theta={x-th:.10f}  1.95*sqrt(x)={D("1.95")*x.sqrt():.10f}  ratio={(x-th)/x.sqrt():.8f}  holds={x-th <= D("1.95")*x.sqrt()}')
print('B. Buthe 2016, Theorem 2 (7.1):  |pi*(x) - li(x)| <= sqrt(x) log(x) / (8 pi)  for x > 59')
for x in (D(96), D('96.5'), D('96.9'), D('96.999999')):
    n = int(x); pis = D(0); k = 1
    while 2**k <= n:
        r = max(m for m in range(1, n + 1) if m**k <= n); pis += D(len(primes(r))) / k; k += 1
    lhs = abs(pis - li(x)); rhs = x.sqrt() * x.ln() / (8 * PI)
    print(f'  x={x}: pi*={pis:.10f}  li={li(x):.10f}  |pi*-li|={lhs:.10f}  bound={rhs:.10f}  holds={lhs <= rhs}')
print('C. Johnston-Yang 2023, Theorem 1.4, for all x >= 23:')
print('   |theta(x)-x| <= 0.027 x (log x)^1.801 exp(-0.1853 (log x)^(3/5) (log log x)^(-1/5))')
print('   |pi(x)-li(x)| <= 0.028 x (log x)^0.801 exp(-0.1853 (log x)^(3/5) (log log x)^(-1/5))')
def vk(c, b, x):
    L = x.ln(); return c * x * (b * L.ln()).exp() * (-D('0.1853') * (D('0.6') * L.ln()).exp() * (D('-0.2') * L.ln().ln()).exp()).exp()
def scan(name, lhs, c, b, hi=200):
    bad = [n for n in range(23, hi) if lhs(n) > vk(c, b, D(n))]
    print(f'   {name} fails at integers {bad[0]}..{bad[-1]} ({len(bad)} of them): {bad}')
theta = lambda n: sum(D(p).ln() for p in primes(n))
scan('theta bound', lambda n: abs(theta(n) - n), D('0.027'), D('1.801'))
scan('pi-li bound (li from 0, as the paper defines it)', lambda n: abs(len(primes(n)) - li(D(n))), D('0.028'), D('0.801'))
LI2 = li(D(2))
scan('pi-Li bound (Li from 2, for comparison)', lambda n: abs(len(primes(n)) - (li(D(n)) - LI2)), D('0.028'), D('0.801'))
for n in (23, 28):
    print(f'   x={n}: theta={theta(n):.8f} |theta-x|={abs(theta(n)-n):.8f} bound={vk(D("0.027"),D("1.801"),D(n)):.8f} | pi={len(primes(n))} li={li(D(n)):.8f} |pi-li|={abs(len(primes(n))-li(D(n))):.8f} bound={vk(D("0.028"),D("0.801"),D(n)):.8f}')

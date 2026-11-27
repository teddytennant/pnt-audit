# pnt-audit

Checks published explicit bounds on π(x), θ(x), ψ(x) and li(x) against the true values, at every
prime power and on both sides of each jump. A bound stated "for all x ≥ x₀" is tested from x₀ up.

## What it found

About 115 inequalities from 17 papers, checked exactly up to 2·10⁷ (10⁸ where thresholds need it)
and by sieve up to 1.6·10¹¹.
Three published theorems fail as stated:

- Büthe, Math. Comp. 87 (2018), Theorem 2, (1.6): `x − θ(x) ≤ 1.95√x` for `1423 ≤ x ≤ 10¹⁹`.
  Fails for every real x in (1426.47, 1427). At x = 1426.9 the left side is 74.077 and the right
  side is 73.660. It holds at every integer. `lean/ButheRefute` proves the negation of the
  statement as formalized in teorth/IEANTN (`Buthe.v1.theorem_2_theta`).
- Büthe, Math. Comp. 85 (2016), Theorem 2, (7.1): `|π*(x) − li(x)| ≤ √x log x / (8π)` for `x > 59`.
  Fails for every real x in (96.29, 97). At x = 96.9 the left side is 1.917 and the right side is
  1.791. Johnston (arXiv:2109.02249, Theorem 1.1) restates the same bound for `x ≥ 59`.
  `lean/ButheRefute/Refute2016.lean` proves the inequality fails at 96.9, and that the IEANTN node
  `Buthe2016.v1.theorem_2_li_minus_riemann_pi` is false given the Riemann hypothesis up to height 30.
- Johnston and Yang, J. Math. Anal. Appl. 527 (2023), Theorem 1.4, stated for all `x ≥ 23`. The θ
  bound fails at the integers 23 to 30, 32 to 40 and 42. The π bound fails at 23 to 60, 63 to 66,
  69 and 70. At x = 23, `|π(x) − li(x)| = 1.884` against a bound of 1.124. The ψ bound holds.
  Checked against arXiv v2; I have not seen the journal's typeset version. `lean/ButheRefute/JY.lean`
  states the θ line as printed and proves it false at x = 28.

Two more that are already fixed in print: Dusart's `x ≥ 88783` (arXiv:1002.0442; the bound fails at
88783 to 88788 and the Ramanujan J. version is cited with 88789, though Wikipedia still says 88783)
and Trudgian's `x ≥ 2898239` (arXiv:1401.2689; fails at 2898240 and 2898241, published as 2898242).

A fourth, in a quoted lemma: `|Q(X) − 6X/π²| ≤ 0.02767√X` for `X ≥ 438653`, with Q the count of
squarefree numbers (Cohen, Dress and El Marraki, as quoted in Lemma 2.1 of Ramaré and Zuniga Alterman,
arXiv:2408.05969). It fails for real X in (441352.8885, 441353) and holds at every integer. I have not
seen the original paper's wording. The Mertens-function bounds in the same paper all hold, with
thresholds exact to the integer.

One trivial one: Axler (arXiv:1703.08032), Proposition 6.1, bounds `∏(1 − 1/p)` above "for every
x > 1" and fails on (1.98, 2), where the product is still empty.

Everything else passed, including Lee and Nosal's bounds and Axler's thresholds at 1.33·10⁹ and
1.9·10¹⁰, which hold with margins as small as 0.01.

The two Büthe failures are filed as teorth/IEANTN #283 and #284.

## Run

Needs Python 3 with numpy, and gcc for the sieve.

```bash
cd num
python3 small.py 2e7          # the unverified IEANTN nodes
python3 dusart2010.py 3e7     # one file per paper: trudgian2016, jy2023, johnston2022, axler2016,
                              # axler2018, leenosal2024
gcc -O2 -o mobius mobius.c -lm && ./mobius 3e8   # Möbius and squarefree sums
python3 confirm.py            # the failures again, in 50-digit decimal arithmetic
gcc -O2 -o sieve sieve.c -lm && ./sieve 1.6e11 < bp.txt   # extremes of the four error terms per range
```

The Lean proofs need a built checkout of teorth/IEANTN; set its path in `lean/ButheRefute/lakefile.toml`
and `lake-manifest.json`, link `.lake/packages` to that checkout's, then `lake build`.

## How a check works

θ, ψ, π and π* only change at prime powers, and between two of them every bound here is monotone in
x. So it is enough to evaluate each bound at each prime power q and in the limit x → q from below.
The second one is where most of the failures are: a threshold was set at a prime, and the bound
breaks just before the next one.

# conjecture searches

Brute-force checks of statements tagged open in google-deepmind/formal-conjectures.

## Found, but not first

OEIS A105720, `a(n) = p_n + p_{n+1} + ... + p_{2n}`. The entry says the terms are squares at "only(?)
three values", n = 3, 6, 4072, and formal-conjectures states that as `OeisA105720`. There is a fourth:

    n = 111008771,  p_n = 2274652151,  p_2n = 4711447171
    a(n) = 387024194082134596 = 622112686^2

`primesq.c` found it and `verify_sq.py` (a separate numpy sieve) confirms the sum; there is no other
square for n <= 2*10^9. It was already reported the day before, 2026-11-26, as
google-deepmind/formal-conjectures #8311.

Colton's conjecture, `pi(n) <= 2 T(n)` for refactorable counts T (OEIS A111291). `../colton/colton.c`
checks every n <= 7.5*10^13: pointwise to 10^9, then a 118-step chain with exact prime counts, every
step with at least 17% to spare. With Zelinsky's Theorem 8 above 7.42*10^13 that settles it. Also not
first: L. Jack's Zenodo note of 2026-11-02 (formal-conjectures #7724) claims the same by a different
route, exact to 10^10 and then Dusart's bounds.

## Checked, no counterexample

- Berndt, Bhat, Meyer, Xie, Zaharescu (arXiv:2501.03234), Conjectures 1.1 and 4.1 to 4.3: every odd
  prime up to 40000 (`berndt.c`).
- Fonollosa (arXiv:2607.08366), Conjecture 1: all n-sets for n = 3..6, and n = 7 for moduli 100..123
  (`minmod.c`).
- Sun's six conjectures on A212496 up to 10^10 (`sun.c`). Four of them are already disproved in
  Mossinghoff and Trudgian (2021), with first failure of `a(n) > sqrt n` at 702469704523413, so the
  "open" tags on those are stale.
- A113010: no fixed point other than 1 and 32 with up to 6000 digits.

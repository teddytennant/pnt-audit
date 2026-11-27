import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import IEANTN.Nodes.Buthe.v1.Conclusions

/-!
# `Buthe.v1.theorem_2_theta` is false

Büthe, *An analytic method for bounding `ψ(x)`*, Math. Comp. 87 (2018), Theorem 2, (1.6):
`x − ϑ(x) ≤ 1.95 √x` for `1423 ≤ x ≤ 10¹⁹`.

At `x = 1426.9` the primes up to `x` are the primes up to `1423`, whose product is below `2 ^ 1952`,
so `ϑ(x) < 1952 log 2 < 1353.03`, and `x − ϑ(x) > 73.87`, while `1.95 √x < 73.67`.
The bound fails on all of `(1426.47, 1427)`; it holds at every integer.
-/

namespace ButheRefute

/-- Trial division by `d, d + 1, …` for at most `k` steps, stopping once `d * d > n`. -/
def noDivisorFrom (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | k + 1, d => n < d * d || (n % d != 0 && noDivisorFrom n k (d + 1))

theorem noDivisorFrom_iff (n k d : ℕ) :
    noDivisorFrom n k d = true ↔ ∀ m, d ≤ m → m < d + k → m * m ≤ n → ¬m ∣ n := by
  induction k generalizing d with
  | zero => simp only [noDivisorFrom, true_iff]; intro m h1 h2; omega
  | succ k ih =>
    simp only [noDivisorFrom, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
      bne_iff_ne, ne_eq, ih]
    constructor
    · rintro (h | ⟨hd, h⟩) m hm1 hm2 hm3
      · exact absurd (Nat.mul_le_mul hm1 hm1) (by omega)
      · rcases hm1.eq_or_lt with rfl | hm1
        · exact fun hdvd ↦ hd (Nat.mod_eq_zero_of_dvd hdvd)
        · exact h m hm1 (by omega) hm3
    · intro h
      by_cases hn : n < d * d
      · exact Or.inl hn
      · exact Or.inr ⟨fun h0 ↦ h d le_rfl (by omega) (by omega) (Nat.dvd_of_mod_eq_zero h0),
          fun m hm1 hm2 ↦ h m (by omega) (by omega)⟩

/-- A primality test the kernel can run quickly. -/
def isPrime (n : ℕ) : Bool := 2 ≤ n && noDivisorFrom n n 2

theorem isPrime_iff (n : ℕ) : isPrime n = true ↔ n.Prime := by
  rw [isPrime, Bool.and_eq_true, decide_eq_true_eq, noDivisorFrom_iff, Nat.prime_def_le_sqrt]
  refine and_congr_right fun _ ↦ forall_congr' fun m ↦ ?_
  constructor
  · exact fun h hm hsq ↦ h hm (by nlinarith [Nat.le_sqrt.mp hsq]) (Nat.le_sqrt.mp hsq)
  · exact fun h hm _ hsq ↦ h hm (Nat.le_sqrt.mpr hsq)

theorem filter_prime (N : ℕ) :
    (Finset.range N).filter Nat.Prime = (Finset.range N).filter (isPrime · = true) :=
  Finset.filter_congr fun n _ ↦ (isPrime_iff n).symm

/-- The product of the primes up to `1426` is below `2 ^ 1952`. -/
theorem primorial_1426 : primorial 1426 ≤ 2 ^ 1952 := by
  rw [primorial, filter_prime]
  decide +kernel

open Real

/-- **Büthe's (1.6) fails at `x = 1426.9`.** -/
theorem theta_counterexample :
    (1.95 : ℝ) * Real.sqrt 1426.9 < 1426.9 - Chebyshev.theta 1426.9 := by
  have hfloor : ⌊(1426.9 : ℝ)⌋₊ = 1426 := by
    rw [Nat.floor_eq_iff (by norm_num)]; norm_num
  have htheta : Chebyshev.theta 1426.9 ≤ 1952 * log 2 := by
    rw [Chebyshev.theta_eq_log_primorial, hfloor]
    calc log (primorial 1426) ≤ log ((2 : ℝ) ^ 1952) :=
          log_le_log (by exact_mod_cast primorial_pos 1426) (by exact_mod_cast primorial_1426)
      _ = 1952 * log 2 := by rw [log_pow]; norm_num
  have hsqrt : Real.sqrt 1426.9 ≤ 37.775 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith [log_two_lt_d9]

/-- The node's statement of Büthe's Theorem 2, (1.6), is false. -/
theorem not_theorem_2_theta : ¬ Buthe.v1.theorem_2_theta := by
  intro h
  have := h 1426.9 (by norm_num) (by norm_num)
  linarith [theta_counterexample]

end ButheRefute

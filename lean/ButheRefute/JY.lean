import Refute

/-!
# Johnston–Yang, Theorem 1.4, the `θ` line, is false at `x = 28`

D. R. Johnston and A. Yang, *Some explicit estimates for the error term in the prime number
theorem*, J. Math. Anal. Appl. 527 (2023), arXiv:2204.01980, Theorem 1.4: for all `x ≥ 23`,
`|θ(x) − x| ≤ 0.027 x (log x)^1.801 exp(−0.1853 (log x)^(3/5) (log log x)^(−1/5))`.

At `x = 28` the left side is `28 − log 223092870 = 8.777` and the right side is `4.574`. The proof
here is crude on purpose: it drops the exponential factor and rounds `1.801` up to `2`, and the
bound still loses, `8.55 < 8.76`.
-/

namespace JYRefute

open Real

/-- Theorem 1.4, second line, as printed. -/
def theorem_1_4_theta : Prop :=
  ∀ x : ℝ, 23 ≤ x →
    |Chebyshev.theta x - x| ≤
      0.027 * x * (log x) ^ (1.801 : ℝ) *
        exp (-0.1853 * (log x) ^ ((3 : ℝ) / 5) * (log (log x)) ^ (-(1 : ℝ) / 5))

theorem primorial_28 : primorial 28 = 223092870 := by
  rw [primorial, ButheRefute.filter_prime]
  decide +kernel

/-- `θ(28) ≤ 27.75 log 2`, from `223092870 ^ 20 ≤ 2 ^ 555`. -/
theorem theta_28_le : Chebyshev.theta 28 ≤ 555 / 20 * log 2 := by
  rw [Chebyshev.theta_eq_log_primorial, Nat.floor_ofNat, primorial_28]
  have h : (20 : ℝ) * log (223092870 : ℝ) ≤ 555 * log 2 := by
    calc (20 : ℝ) * log (223092870 : ℝ) = log ((223092870 : ℝ) ^ 20) := by rw [log_pow]; norm_num
      _ ≤ log ((2 : ℝ) ^ 555) :=
          log_le_log (by positivity)
            (by exact_mod_cast (by decide +kernel : (223092870 : ℕ) ^ 20 ≤ 2 ^ 555))
      _ = 555 * log 2 := by rw [log_pow]; norm_num
  push_cast
  linarith

/-- `log 28 ≤ 4.85 log 2`, from `28 ^ 20 ≤ 2 ^ 97`. -/
theorem log_28_le : log 28 ≤ 97 / 20 * log 2 := by
  have h : (20 : ℝ) * log 28 ≤ 97 * log 2 := by
    calc (20 : ℝ) * log 28 = log ((28 : ℝ) ^ 20) := by rw [log_pow]; norm_num
      _ ≤ log ((2 : ℝ) ^ 97) := log_le_log (by positivity) (by norm_num)
      _ = 97 * log 2 := by rw [log_pow]; norm_num
  linarith

theorem one_le_log_28 : 1 ≤ log 28 := by
  have h : 2 * log 2 ≤ log 28 := by
    calc 2 * log 2 = log ((2 : ℝ) ^ 2) := by rw [log_pow]; norm_num
      _ ≤ log 28 := log_le_log (by positivity) (by norm_num)
  linarith [log_two_gt_d9]

theorem not_theorem_1_4_theta : ¬ theorem_1_4_theta := by
  intro h
  have h28 := h 28 (by norm_num)
  have hL1 := one_le_log_28
  have hL2 : log 28 ≤ 3.362 := by linarith [log_28_le, log_two_lt_d9]
  -- the power: `(log 28) ^ 1.801 ≤ (log 28) ^ 2 ≤ 3.362 ^ 2`
  have hpow : (log 28) ^ (1.801 : ℝ) ≤ 11.304 := by
    calc (log 28) ^ (1.801 : ℝ) ≤ (log 28) ^ (2 : ℝ) :=
          rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = (log 28) ^ 2 := rpow_two _
      _ ≤ 11.304 := by nlinarith
  have hpow0 : 0 ≤ (log 28) ^ (1.801 : ℝ) := rpow_nonneg (by linarith) _
  -- the exponential factor is at most one
  have hA : 0 ≤ (log 28) ^ ((3 : ℝ) / 5) := rpow_nonneg (by linarith) _
  have hB : 0 ≤ (log (log 28)) ^ (-(1 : ℝ) / 5) := rpow_nonneg (log_nonneg hL1) _
  have hexp : exp (-0.1853 * (log 28) ^ ((3 : ℝ) / 5) * (log (log 28)) ^ (-(1 : ℝ) / 5)) ≤ 1 := by
    rw [exp_le_one_iff]
    have := mul_nonneg hA hB
    nlinarith
  have hexp0 := exp_pos (-0.1853 * (log 28) ^ ((3 : ℝ) / 5) * (log (log 28)) ^ (-(1 : ℝ) / 5))
  have hrhs : 0.027 * 28 * (log 28) ^ (1.801 : ℝ) *
      exp (-0.1853 * (log 28) ^ ((3 : ℝ) / 5) * (log (log 28)) ^ (-(1 : ℝ) / 5)) ≤ 8.546 := by
    calc 0.027 * 28 * (log 28) ^ (1.801 : ℝ) *
          exp (-0.1853 * (log 28) ^ ((3 : ℝ) / 5) * (log (log 28)) ^ (-(1 : ℝ) / 5))
        ≤ 0.027 * 28 * (log 28) ^ (1.801 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ 8.546 := by nlinarith
  have hlhs : 8.76 ≤ |Chebyshev.theta 28 - 28| := by
    have := neg_abs_le (Chebyshev.theta 28 - 28)
    linarith [theta_28_le, log_two_lt_d9]
  linarith

end JYRefute

import Refute
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import IEANTN.Nodes.Buthe2016.v1.Conclusions

/-!
# `Buthe2016.v1.theorem_2_li_minus_riemann_pi` is false at `x = 96.9`

Büthe, *Estimating `π(x)` and related functions under partial RH assumptions*, Math. Comp. 85
(2016), Theorem 2, (7.1): `|π*(x) − li(x)| ≤ √x log x / (8π)` for `59 < x` with
`4.92 √(x / log x) ≤ T`, given the Riemann hypothesis up to height `T`.

At `x = 96.9` we have `π*(x) = 413/15 ≈ 27.533`, `li(x) ≈ 29.451` and `√x log x / (8π) ≈ 1.791`,
so the bound misses by `0.126`. The range condition needs only `T ≥ 24`, well inside the verified
range, so the node's statement fails for `T = 30`.

The proof bounds `li 96.9 = li 2 + Li 96.9` from below:

* `li 2 = ∫₀² g ≥ ∫₀² 3 / (5 + t) = 3 log (7/5)`, where `g t = 1 / log t − 1 / (t − 1)`, from the
  Padé bound `log t ≤ (t − 1)(t + 5) / (4t + 2)` (`log_le_pade`);
* `Li 96.9 ≥ 28.37` by the midpoint rule on 24 blocks, which is a lower bound because `1 / log` is
  convex. Every logarithm is bounded through `log 2`, from integer comparisons `p ^ k ≤ 2 ^ j q ^ k`
  checked by the kernel.

The `li` machinery (`g`, `li_eq`, `midpoint_le_integral`) is copied from
`IEANTN/Solutions/ButheNumerics.v2/LogIntegral.lean`, which lives in a different Lake project.
-/

open Real MeasureTheory Set Filter Topology

namespace Buthe2016Refute

/-! ### `li` as `log (x - 1)` plus an honest integral -/

/-- `1 / log t` with its pole at `t = 1` subtracted off. -/
noncomputable def g (t : ℝ) : ℝ := 1 / log t - 1 / (t - 1)

theorem g_mem_Icc {t : ℝ} (ht : 0 < t) : g t ∈ Icc 0 1 := by
  rcases eq_or_ne t 1 with rfl | h1
  · simp [g]
  have hP : 0 < log t * (t - 1) := by
    rcases lt_or_gt_of_ne h1 with h | h
    · exact mul_pos_of_neg_of_neg (log_neg ht h) (by linarith)
    · exact mul_pos (log_pos h) (by linarith)
  have hu := log_le_sub_one_of_pos ht
  have hl := one_sub_inv_le_log_of_pos ht
  have hg : g t = (t - 1 - log t) / (log t * (t - 1)) := by
    have : log t ≠ 0 := by rintro h; simp [h] at hP
    have : t - 1 ≠ 0 := sub_ne_zero.mpr h1
    simp only [g]
    field_simp
  rw [hg]
  refine ⟨div_nonneg (by linarith) hP.le, (div_le_one hP).mpr ?_⟩
  have : 1 - t⁻¹ = (t - 1) / t := by field_simp
  rw [this, div_le_iff₀ ht] at hl
  nlinarith

theorem measurable_g : Measurable g := by
  unfold g
  fun_prop

theorem integrableOn_g (x : ℝ) : IntegrableOn g (Ioc 0 x) := by
  refine Measure.integrableOn_of_bounded (M := 1) (by simp) measurable_g.aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ ?_
  have := g_mem_Icc ht.1
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [this.1], this.2⟩

/-- `∫ 1 / (t - 1)` over the two sides of the pole: the two `log ε` cancel. -/
theorem integral_pole {x ε : ℝ} (hx : 2 ≤ x) (hε : ε ∈ Ioo 0 1) :
    ∫ t in Ioc 0 (1 - ε) ∪ Icc (1 + ε) x, 1 / (t - 1) = log (x - 1) := by
  obtain ⟨hε0, hε1⟩ := hε
  have hc₁ : ContinuousOn (fun t : ℝ ↦ 1 / (t - 1)) (Icc 0 (1 - ε)) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht ↦ ?_
    linarith [ht.2]
  have hc₂ : ContinuousOn (fun t : ℝ ↦ 1 / (t - 1)) (Icc (1 + ε) x) := by
    refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht ↦ ?_
    linarith [ht.1]
  rw [setIntegral_union (Set.disjoint_left.mpr fun t h₁ h₂ ↦ by linarith [h₁.2, h₂.1])
    measurableSet_Icc
    ((hc₁.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self)
    (hc₂.integrableOn_compact isCompact_Icc),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_sub_right (fun t ↦ 1 / t),
    intervalIntegral.integral_comp_sub_right (fun t ↦ 1 / t),
    integral_one_div, integral_one_div]
  · rw [show (1 - ε - 1) / (0 - 1) = ε by ring, show 1 + ε - 1 = ε by ring,
      log_div (by linarith) hε0.ne']
    ring
  · rw [mem_uIcc]; rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> linarith
  · rw [mem_uIcc]; rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> linarith

/-- The principal value `li x` is `log (x - 1)` plus an honest integral of the bounded `g`. -/
theorem li_eq {x : ℝ} (hx : 2 ≤ x) : IEANTN.li x = log (x - 1) + ∫ t in Ioc 0 x, g t := by
  have hg := integrableOn_g x
  have hsplit : ∀ ε ∈ Ioo (0 : ℝ) 1,
      (∫ t in Ioc 0 x \ Ioo (1 - ε) (1 + ε), 1 / log t) =
        log (x - 1) + (∫ t in Ioc 0 x, g t) - ∫ t in Ioo (1 - ε) (1 + ε), g t := by
    intro ε hε
    have hsub : Ioo (1 - ε) (1 + ε) ⊆ Ioc 0 x := fun t ht ↦
      ⟨by linarith [ht.1, hε.2], by linarith [ht.2, hε.2]⟩
    have hS : Ioc 0 x \ Ioo (1 - ε) (1 + ε) = Ioc 0 (1 - ε) ∪ Icc (1 + ε) x := by
      ext t
      simp only [Set.mem_sdiff, mem_Ioc, mem_Ioo, mem_union, mem_Icc, not_and_or, not_lt]
      constructor
      · rintro ⟨⟨h0, hx'⟩, h | h⟩
        · exact Or.inl ⟨h0, h⟩
        · exact Or.inr ⟨h, hx'⟩
      · rintro (⟨h0, h⟩ | ⟨h, hx'⟩)
        · exact ⟨⟨h0, by linarith [hε.1]⟩, Or.inl h⟩
        · exact ⟨⟨by linarith [hε.1], hx'⟩, Or.inr h⟩
    have hpole : IntegrableOn (fun t : ℝ ↦ 1 / (t - 1)) (Ioc 0 x \ Ioo (1 - ε) (1 + ε)) := by
      rw [hS]
      refine IntegrableOn.union ?_ ?_
      · refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set Ioc_subset_Icc_self
        refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht ↦ ?_
        linarith [ht.2, hε.1]
      · refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
        refine ContinuousOn.div continuousOn_const (by fun_prop) fun t ht ↦ ?_
        linarith [ht.1, hε.1]
    have : (fun t ↦ 1 / log t) = fun t ↦ g t + 1 / (t - 1) := by ext t; simp [g]
    rw [this, integral_add (hg.mono_set sdiff_subset) hpole,
      setIntegral_sdiff measurableSet_Ioo hg hsub, hS, integral_pole hx hε]
    ring
  have hsmall : Tendsto (fun ε ↦ ∫ t in Ioo (1 - ε) (1 + ε), g t) (𝓝[>] 0) (𝓝 0) := by
    have h2 : Tendsto (fun ε : ℝ ↦ 2 * ε) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((continuous_const_mul (2 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    refine (norm_setIntegral_le_of_norm_le_const (C := 1) measure_Ioo_lt_top
      fun t ht ↦ ?_).trans_eq ?_
    · have := g_mem_Icc (show 0 < t by linarith [ht.1, hε.2])
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [this.1], this.2⟩
    · rw [Real.volume_real_Ioo_of_le (by linarith [hε.1])]
      ring
  refine Tendsto.limUnder_eq ?_
  have hev : (fun ε ↦ log (x - 1) + (∫ t in Ioc 0 x, g t) - ∫ t in Ioo (1 - ε) (1 + ε), g t)
      =ᶠ[𝓝[>] 0] fun ε ↦ ∫ t in Ioc 0 x \ Ioo (1 - ε) (1 + ε), 1 / log t := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
    exact (hsplit ε hε).symm
  refine Tendsto.congr' hev ?_
  simpa using (tendsto_const_nhds (x := log (x - 1) + ∫ t in Ioc 0 x, g t)).sub hsmall

theorem intervalIntegrable_inv_log {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t ↦ 1 / log t) volume a b :=
  ContinuousOn.intervalIntegrable fun t ht ↦ by
    rw [uIcc_of_le hab] at ht
    exact (continuousAt_const.div (continuousAt_log (by linarith [ht.1]))
      (log_pos (by linarith [ht.1])).ne').continuousWithinAt

/-- `li x = li 2 + Li x`, with `li 2` written as `∫₀² g`. -/
theorem li_eq_add_Li {x : ℝ} (hx : 2 ≤ x) :
    IEANTN.li x = (∫ t in Ioc 0 2, g t) + IEANTN.Li x := by
  have hpole : IntervalIntegrable (fun t : ℝ ↦ 1 / (t - 1)) volume 2 x := by
    refine ContinuousOn.intervalIntegrable fun t ht ↦ ?_
    rw [uIcc_of_le hx] at ht
    exact (continuousAt_const.div (by fun_prop) (by linarith [ht.1])).continuousWithinAt
  have h2x : ∫ t in (2 : ℝ)..x, g t = IEANTN.Li x - log (x - 1) := by
    rw [IEANTN.Li]
    simp only [g]
    rw [intervalIntegral.integral_sub (intervalIntegrable_inv_log (by norm_num) hx) hpole,
      intervalIntegral.integral_comp_sub_right (fun t ↦ 1 / t), integral_one_div]
    · norm_num
    · rw [mem_uIcc]; rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) <;> linarith
  have hg02 : IntervalIntegrable g volume 0 2 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mpr (integrableOn_g 2)
  have hg2x : IntervalIntegrable g volume 2 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).mpr
      ((integrableOn_g x).mono_set (Ioc_subset_Ioc_left (by norm_num)))
  rw [li_eq hx, ← intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ x),
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
    ← intervalIntegral.integral_add_adjacent_intervals hg02 hg2x, h2x]
  ring

/-! ### Logarithms through `log 2` -/

/-- `log (p / q) ≤ (j / k) log 2` from `p ^ k ≤ 2 ^ j q ^ k`. -/
theorem log_le_of_pow {p q k j : ℕ} (h : 0 < p ∧ 0 < q ∧ 0 < k ∧ p ^ k ≤ 2 ^ j * q ^ k) :
    log ((p : ℝ) / q) ≤ j / k * log 2 := by
  obtain ⟨hp, hq, hk, h⟩ := h
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hpow : ((p : ℝ) / q) ^ k ≤ 2 ^ j := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    exact_mod_cast h
  have := log_le_log (by positivity) hpow
  rw [log_pow, log_pow] at this
  rw [div_mul_eq_mul_div, le_div_iff₀ hk']
  linarith

/-- `(j / k) log 2 ≤ log (p / q)` from `2 ^ j q ^ k ≤ p ^ k`. -/
theorem le_log_of_pow {p q k j : ℕ} (h : 0 < q ∧ 0 < k ∧ 2 ^ j * q ^ k ≤ p ^ k) :
    j / k * log 2 ≤ log ((p : ℝ) / q) := by
  obtain ⟨hq, hk, h⟩ := h
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hpow : (2 : ℝ) ^ j ≤ ((p : ℝ) / q) ^ k := by
    rw [div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast h
  have := log_le_log (by positivity) hpow
  rw [log_pow, log_pow] at this
  rw [div_mul_eq_mul_div, div_le_iff₀ hk']
  linarith

/-! ### `Li 96.9`, by the midpoint rule -/

/-- The tangent line to `1 / log` at `m` lies below it. -/
theorem tangent_le_inv_log {m t : ℝ} (hm : 1 < m) (ht : 1 < t) :
    1 / log m - (t - m) / (m * log m ^ 2) ≤ 1 / log t := by
  have hL := log_pos hm
  have hu := log_pos ht
  have hm0 : 0 < m := by linarith
  have h := log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < t) hm0)
  rw [log_div (by linarith) hm0.ne'] at h
  have h' : log t - log m ≤ (t - m) / m := by rw [sub_div, div_self hm0.ne']; exact h
  calc 1 / log m - (t - m) / (m * log m ^ 2)
      = 1 / log m - (t - m) / m / log m ^ 2 := by rw [div_div]
    _ ≤ 1 / log m - (log t - log m) / log m ^ 2 := by gcongr
    _ ≤ 1 / log t := by
      rw [← sub_nonneg]
      have : 1 / log t - (1 / log m - (log t - log m) / log m ^ 2) =
          (log m - log t) ^ 2 / (log t * log m ^ 2) := by
        field_simp
        ring
      rw [this]
      positivity

/-- The midpoint rule is a lower bound for the convex `1 / log t`. -/
theorem midpoint_le_integral {a b c : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hc : log ((a + b) / 2) ≤ c) :
    (b - a) / c ≤ ∫ t in a..b, 1 / log t := by
  set m := (a + b) / 2
  have hm : 1 < m := by simp only [m]; linarith
  have hL := log_pos hm
  have hlin : Continuous fun t : ℝ ↦ 1 / log m - (t - m) / (m * log m ^ 2) := by fun_prop
  calc (b - a) / c ≤ (b - a) / log m := by
        gcongr
    _ = ∫ t in a..b, (1 / log m - (t - m) / (m * log m ^ 2)) := by
        have h1 : ∫ t in a..b, (t - m) / (m * log m ^ 2) = 0 := by
          rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_right (fun t ↦ t),
            integral_id]
          simp only [m]
          ring
        rw [intervalIntegral.integral_sub intervalIntegrable_const
          ((by fun_prop : Continuous fun t : ℝ ↦ (t - m) / (m * log m ^ 2)).intervalIntegrable _ _),
          h1, intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_one_div]
    _ ≤ ∫ t in a..b, 1 / log t := by
        refine intervalIntegral.integral_mono_on hab (hlin.intervalIntegrable _ _)
          (intervalIntegrable_inv_log ha hab) fun t ht ↦
            tangent_le_inv_log hm (by linarith [ht.1])

/-- One midpoint block `[a, b]`, with `(a + b) / 2 = p / q` and `log (p / q) ≤ (j / k) log 2`,
followed by the rest of the integral up to `c`. -/
theorem block {a b c v : ℝ} {p q k j : ℕ} (ha : 1 < a) (hab : a ≤ b) (hbc : b ≤ c)
    (hm : (a + b) / 2 = p / q) (h : 0 < p ∧ 0 < q ∧ 0 < k ∧ p ^ k ≤ 2 ^ j * q ^ k)
    (hrest : v ≤ ∫ t in b..c, 1 / log t) :
    (b - a) / (j / k * 0.6931471808) + v ≤ ∫ t in a..c, 1 / log t := by
  have hlog : log ((a + b) / 2) ≤ j / k * 0.6931471808 := by
    rw [hm]
    refine (log_le_of_pow h).trans ?_
    gcongr
    exact log_two_lt_d9.le
  rw [← intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_inv_log ha hab)
    (intervalIntegrable_inv_log (by linarith) hbc)]
  linarith [midpoint_le_integral ha hab hlog]

/-- `Li 96.9 ≥ 28.37`; the true value is `28.4055…`. -/
theorem Li_ge : (28.37 : ℝ) ≤ IEANTN.Li 96.9 := by
  have h := block (a := 2) (b := 2.5) (p := 9) (q := 4) (k := 100) (j := 117)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 2.5) (b := 3) (p := 11) (q := 4) (k := 37) (j := 54)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 3) (b := 3.5) (p := 13) (q := 4) (k := 137) (j := 233)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 3.5) (b := 4) (p := 15) (q := 4) (k := 43) (j := 82)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 4) (b := 5) (p := 9) (q := 2) (k := 47) (j := 102)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 5) (b := 6) (p := 11) (q := 2) (k := 37) (j := 91)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 6) (b := 7) (p := 13) (q := 2) (k := 107) (j := 289)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 7) (b := 8) (p := 15) (q := 2) (k := 43) (j := 125)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 8) (b := 10) (p := 9) (q := 1) (k := 47) (j := 149)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 10) (b := 12) (p := 11) (q := 1) (k := 37) (j := 128)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 12) (b := 14) (p := 13) (q := 1) (k := 87) (j := 322)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 14) (b := 16) (p := 15) (q := 1) (k := 43) (j := 168)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 16) (b := 20) (p := 18) (q := 1) (k := 41) (j := 171)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 20) (b := 24) (p := 22) (q := 1) (k := 37) (j := 165)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 24) (b := 28) (p := 26) (q := 1) (k := 77) (j := 362)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 28) (b := 32) (p := 30) (q := 1) (k := 43) (j := 211)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 32) (b := 40) (p := 36) (q := 1) (k := 41) (j := 212)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 40) (b := 48) (p := 44) (q := 1) (k := 37) (j := 202)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 48) (b := 56) (p := 52) (q := 1) (k := 67) (j := 382)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 56) (b := 64) (p := 60) (q := 1) (k := 43) (j := 254)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 64) (b := 72) (p := 68) (q := 1) (k := 34) (j := 207)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 72) (b := 80) (p := 76) (q := 1) (k := 121) (j := 756)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 80) (b := 88) (p := 84) (q := 1) (k := 28) (j := 179)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel) <|
    block (a := 88) (b := 96.9) (p := 1849) (q := 20) (k := 32) (j := 209)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide +kernel)
    (le_of_eq (intervalIntegral.integral_same).symm)
  rw [IEANTN.Li]
  norm_num at h ⊢
  linarith

/-! ### `li 2`, from a Padé bound for `log` -/

/-- The gap in `log t ≤ (t - 1)(t + 5) / (4t + 2)`. -/
noncomputable def pade (t : ℝ) : ℝ := (t - 1) * (t + 5) / (4 * t + 2) - log t

theorem hasDerivAt_pade {t : ℝ} (ht : 0 < t) :
    HasDerivAt pade (4 * (t - 1) ^ 3 / ((4 * t + 2) ^ 2 * t)) t := by
  have hne : 4 * t + 2 ≠ 0 := by positivity
  have h := ((((hasDerivAt_id t).sub_const 1).mul ((hasDerivAt_id t).add_const 5)).div
    (((hasDerivAt_id t).const_mul 4).add_const 2) hne).sub (hasDerivAt_log ht.ne')
  have h2 : HasDerivAt pade _ t := h
  refine h2.congr_deriv ?_
  simp only [id, Pi.mul_apply]
  field_simp
  ring

/-- `log t ≤ (t - 1)(t + 5) / (4t + 2)` for `t > 0`: the gap has derivative
`4 (t - 1)³ / ((4t + 2)² t)`, so it is smallest at `t = 1`, where it is zero. -/
theorem log_le_pade {t : ℝ} (ht : 0 < t) : log t ≤ (t - 1) * (t + 5) / (4 * t + 2) := by
  have hcont : ∀ s : Set ℝ, s ⊆ Ioi 0 → ContinuousOn pade s := fun s hs x hx ↦
    (hasDerivAt_pade (hs hx)).continuousAt.continuousWithinAt
  have hdiff : ∀ s : Set ℝ, s ⊆ Ioi 0 → DifferentiableOn ℝ pade s := fun s hs x hx ↦
    (hasDerivAt_pade (hs hx)).differentiableAt.differentiableWithinAt
  have h1 : pade 1 = 0 := by norm_num [pade]
  suffices 0 ≤ pade t by unfold pade at this; linarith
  rcases le_total 1 t with h | h
  · have hmono : MonotoneOn pade (Ici 1) := by
      refine monotoneOn_of_deriv_nonneg (convex_Ici 1)
        (hcont _ fun x hx ↦ mem_Ioi.mpr (lt_of_lt_of_le one_pos hx))
        (hdiff _ fun x hx ↦ by rw [interior_Ici] at hx; exact mem_Ioi.mpr (lt_trans one_pos hx)) ?_
      intro x hx
      rw [interior_Ici] at hx
      have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
      rw [(hasDerivAt_pade hx0).deriv]
      exact div_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by linarith [mem_Ioi.mp hx]) 3))
        (by positivity)
    rw [← h1]
    exact hmono (mem_Ici.mpr le_rfl) h h
  · have hanti : AntitoneOn pade (Ioc 0 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Ioc 0 1) (hcont _ fun x hx ↦ hx.1)
        (hdiff _ fun x hx ↦ by rw [interior_Ioc] at hx; exact hx.1) ?_
      intro x hx
      rw [interior_Ioc] at hx
      rw [(hasDerivAt_pade hx.1).deriv]
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by norm_num)
          ((Odd.pow_nonpos_iff ⟨1, rfl⟩).mpr (by linarith [hx.2])))
        (by have := hx.1; positivity)
    rw [← h1]
    exact hanti ⟨ht, h⟩ ⟨one_pos, le_rfl⟩ h

/-- `g t ≥ 3 / (5 + t)` away from the pole. -/
theorem g_ge {t : ℝ} (ht : 0 < t) (h1 : t ≠ 1) : 3 * (5 + t)⁻¹ ≤ g t := by
  have hP := log_le_pade ht
  have hD : 0 < 4 * t + 2 := by positivity
  have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr h1
  have key : (4 * t + 2) / ((t - 1) * (t + 5)) ≤ 1 / log t := by
    rw [← one_div_div]
    rcases lt_or_gt_of_ne h1 with h | h
    · have hR : (t - 1) * (t + 5) / (4 * t + 2) < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith) (by linarith)) hD
      exact (one_div_le_one_div_of_neg hR (log_neg ht h)).mpr hP
    · exact one_div_le_one_div_of_le (log_pos h) hP
  have e : (4 * t + 2) / ((t - 1) * (t + 5)) = 1 / (t - 1) + 3 * (5 + t)⁻¹ := by
    have : t + 5 ≠ 0 := by positivity
    have : 5 + t ≠ 0 := by positivity
    field_simp
    ring
  unfold g
  linarith

/-- `li 2 = ∫₀² g ≥ 3 log (7/5) ≈ 1.0094`; the true value is `1.0451…`. -/
theorem li_two_ge : 3 * log (7 / 5) ≤ ∫ t in Ioc 0 2, g t := by
  have hint : ∫ t in Ioc 0 2, 3 * (5 + t)⁻¹ = 3 * log (7 / 5) := by
    rw [← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_left (fun t ↦ t⁻¹) 5,
      integral_inv_of_pos (by norm_num) (by norm_num)]
    norm_num
  rw [← hint]
  refine integral_mono_ae ?_ (integrableOn_g 2) ?_
  · refine (ContinuousOn.integrableOn_compact isCompact_Icc ?_).mono_set Ioc_subset_Icc_self
    exact continuousOn_const.mul (ContinuousOn.inv₀ (by fun_prop)
      fun t ht ↦ (by linarith [ht.1] : (0 : ℝ) < 5 + t).ne')
  · filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr (measure_singleton (1 : ℝ))),
      ae_restrict_mem measurableSet_Ioc] with t h1 ht
    exact g_ge ht.1 h1

/-! ### `π*(96.9) ≤ 413/15` -/

theorem primeCounting_eq (N v : ℕ) (h : ((Finset.range (N + 1)).filter
    (ButheRefute.isPrime · = true)).card = v) : Nat.primeCounting N = v := by
  rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range,
    ButheRefute.filter_prime, h]

/-- The `k`-th term of `π*(96.9)` is at most `π(N) / (k + 1)` when `96.9 < (N + 1) ^ (k + 1)`. -/
theorem term_le (k N : ℕ) (P d : ℝ) (hd : (k : ℝ) + 1 = d) (hP : (Nat.primeCounting N : ℝ) ≤ P)
    (hx : (96.9 : ℝ) < ((N : ℝ) + 1) ^ (k + 1)) :
    IEANTN.primeCounting ((96.9 : ℝ) ^ (1 / ((k : ℝ) + 1))) / ((k : ℝ) + 1) ≤ P / d := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hy0 : 0 ≤ (96.9 : ℝ) ^ (1 / ((k : ℝ) + 1)) := by positivity
  have hy : (96.9 : ℝ) ^ (1 / ((k : ℝ) + 1)) < (N : ℝ) + 1 := by
    rw [one_div, rpow_inv_lt_iff_of_pos (by norm_num) (by positivity) hk,
      show (k : ℝ) + 1 = ((k + 1 : ℕ) : ℝ) by push_cast; ring, rpow_natCast]
    exact hx
  have hfl : ⌊(96.9 : ℝ) ^ (1 / ((k : ℝ) + 1))⌋₊ ≤ N :=
    Nat.lt_succ_iff.mp ((Nat.floor_lt hy0).mpr (by push_cast; exact hy))
  rw [← hd, IEANTN.primeCounting]
  gcongr
  exact (Nat.cast_le.mpr (Nat.monotone_primeCounting hfl)).trans hP

theorem riemannPrimeCounting_le : IEANTN.riemannPrimeCounting 96.9 ≤ 413 / 15 := by
  have p96 := primeCounting_eq 96 24 (by decide +kernel)
  have p9 := primeCounting_eq 9 4 (by decide +kernel)
  have p4 := primeCounting_eq 4 2 (by decide +kernel)
  have p3 := primeCounting_eq 3 2 (by decide +kernel)
  have p2 := primeCounting_eq 2 1 (by decide +kernel)
  have p1 := primeCounting_eq 1 0 (by decide +kernel)
  rw [IEANTN.riemannPrimeCounting, tsum_eq_sum (s := Finset.range 6)]
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have h0 := term_le 0 96 24 1 (by norm_num) (by rw [p96]; norm_num) (by norm_num)
    have h1 := term_le 1 9 4 2 (by norm_num) (by rw [p9]; norm_num) (by norm_num)
    have h2 := term_le 2 4 2 3 (by norm_num) (by rw [p4]; norm_num) (by norm_num)
    have h3 := term_le 3 3 2 4 (by norm_num) (by rw [p3]; norm_num) (by norm_num)
    have h4 := term_le 4 2 1 5 (by norm_num) (by rw [p2]; norm_num) (by norm_num)
    have h5 := term_le 5 2 1 6 (by norm_num) (by rw [p2]; norm_num) (by norm_num)
    linarith
  · intro k hk
    rw [Finset.mem_range, not_lt] at hk
    have hk1 : (0 : ℝ) ≤ (k : ℝ) + 1 := (Nat.cast_add_one_pos k).le
    have hpc : 0 ≤ IEANTN.primeCounting ((96.9 : ℝ) ^ (1 / ((k : ℝ) + 1))) := Nat.cast_nonneg _
    have h0 := div_nonneg hpc hk1
    refine le_antisymm ?_ h0
    have := term_le k 1 0 ((k : ℝ) + 1) rfl (by rw [p1]; norm_num) ?_
    · rwa [zero_div] at this
    · calc (96.9 : ℝ) < 2 ^ 7 := by norm_num
        _ ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        _ = ((1 : ℕ) + 1 : ℝ) ^ (k + 1) := by norm_num

/-! ### The counterexample -/

theorem log_969_le : log 96.9 ≤ 4.5748 := by
  have h := log_le_of_pow (p := 969) (q := 10) (k := 10) (j := 66) (by decide +kernel)
  norm_num at h ⊢
  linarith [log_two_lt_d9]

theorem log_969_ge : 4.15 ≤ log 96.9 := by
  have h := le_log_of_pow (p := 969) (q := 10) (k := 1) (j := 6) (by decide +kernel)
  norm_num at h ⊢
  linarith [log_two_gt_d9]

theorem li_ge : 29.378 ≤ IEANTN.li 96.9 := by
  have h := le_log_of_pow (p := 7) (q := 5) (k := 33) (j := 16) (by decide +kernel)
  have h75 : 1.00821 ≤ 3 * log (7 / 5) := by
    norm_num at h ⊢
    linarith [log_two_gt_d9]
  rw [li_eq_add_Li (by norm_num)]
  linarith [li_two_ge, Li_ge]

/-- **(7.1) fails at `x = 96.9`.** -/
theorem li_counterexample :
    Real.sqrt 96.9 * Real.log 96.9 / (8 * Real.pi) <
      |IEANTN.riemannPrimeCounting 96.9 - IEANTN.li 96.9| := by
  have hs : Real.sqrt 96.9 ≤ 9.8438 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hl := log_969_le
  have hl0 : 0 ≤ log 96.9 := by linarith [log_969_ge]
  have hR : Real.sqrt 96.9 * Real.log 96.9 / (8 * Real.pi) ≤ 1.792 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul hs hl hl0 (by norm_num), pi_gt_d6]
  have := neg_abs_le (IEANTN.riemannPrimeCounting 96.9 - IEANTN.li 96.9)
  linarith [riemannPrimeCounting_le, li_ge]

theorem withinRange_30 : Buthe2016.v1.withinRange 30 96.9 := by
  have hl := log_969_ge
  have hs : Real.sqrt (96.9 / log 96.9) ≤ 5 := by
    rw [Real.sqrt_le_left (by norm_num), div_le_iff₀ (by linarith)]
    linarith
  unfold Buthe2016.v1.withinRange
  linarith

/-- The node's statement of Büthe's (7.1) is false, given the Riemann hypothesis to height `30`. -/
theorem not_theorem_2_li_minus_riemann_pi (h : IEANTN.RiemannHypothesisUpTo 30) :
    ¬ Buthe2016.v1.theorem_2_li_minus_riemann_pi := by
  intro hn
  have := hn 30 h 96.9 (by norm_num) withinRange_30
  linarith [li_counterexample]

end Buthe2016Refute

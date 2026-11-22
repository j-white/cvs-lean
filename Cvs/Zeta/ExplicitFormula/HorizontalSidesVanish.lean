import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The horizontal sides vanish

Mathlib's rectangle Cauchy theorem, at `z = ½ − iR` and `w = 2 + iR`, reads
-/

namespace Cvs.Zeta.ExplicitFormula.HorizontalSidesVanish

open Complex MeasureTheory
open scoped Real

/-- `(1 + log(2+R))/(1+R)³ ≤ 3/(1+R)²` for `R ≥ 0` — enough to kill the
horizontal, with no need for a sharp `log` estimate. -/
theorem log_bound {R : ℝ} (hR : 0 ≤ R) :
    (1 + Real.log (2 + R)) / (1 + R) ^ 3 ≤ 3 / (1 + R) ^ 2 := by
  have h2 : (0 : ℝ) < 2 + R := by linarith
  have hlog : Real.log (2 + R) ≤ 1 + R := by
    have := Real.log_le_sub_one_of_pos h2
    linarith
  have hpos : (0 : ℝ) < (1 + R) ^ 3 := by positivity
  have hpos2 : (0 : ℝ) < (1 + R) ^ 2 := by positivity
  rw [div_le_div_iff₀ hpos hpos2]
  nlinarith [hR, sq_nonneg (1 + R)]

theorem tendsto_three_div_sq : Filter.Tendsto (fun R : ℝ => 3 / (1 + R) ^ 2)
    Filter.atTop (nhds 0) := by
  have hb : Filter.Tendsto (fun R : ℝ => (1 + R) ^ 2) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono' _ ?_ Filter.tendsto_id
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with R hR
    simp only [id_eq]
    nlinarith
  have h2 := tendsto_inv_atTop_zero.comp hb
  have h3 := h2.const_mul (3 : ℝ)
  rw [mul_zero] at h3
  exact h3.congr fun R => (div_eq_mul_inv 3 ((1 + R) ^ 2)).symm

end Cvs.Zeta.ExplicitFormula.HorizontalSidesVanish

import Mathlib
import Cvs.WeilForm.Archimedean.LevyDensity

/-!
# The density is a genuine Lévy measure

    ∫₀^∞ min(1, u²) · densityU u  du  <  ∞

The `1/u` pole at the origin is killed by `u²`, the tail by `e^{−u/4}`; one bound
`min(1,u²)·densityU u ≤ 2e^{−u/4}` carries both.
-/

set_option maxHeartbeats 1600000

noncomputable section

open Real MeasureTheory Set

namespace Cvs.WeilForm.Archimedean.LevyMeasure

open Cvs.WeilForm.Archimedean.LevyDensity

/-- The denominator, from below: `1 + x ≤ e^x` gives `1 − e^{−u} ≥ u/(1+u)`. -/
theorem le_one_sub_exp {u : ℝ} (hu : 0 < u) : u / (1 + u) ≤ 1 - Real.exp (-u) := by
  have hpos : (0:ℝ) < 1 + u := by linarith
  have hexp : 1 + u ≤ Real.exp u := by have := Real.add_one_le_exp u; linarith
  have hinv : Real.exp (-u) ≤ 1 / (1 + u) := by
    rw [Real.exp_neg, one_div]; gcongr
  have heq : u / (1 + u) = 1 - 1 / (1 + u) := by field_simp; ring
  rw [heq]; linarith

/-- **The density, bounded exactly** — the `1/u` pole and the `e^{−u/4}` tail together. -/
theorem densityU_le {u : ℝ} (hu : 0 < u) :
    densityU u ≤ (1 + u) * Real.exp (-(u / 4)) / u := by
  unfold densityU
  have h1 : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hd : (0:ℝ) < 1 - Real.exp (-u) := by linarith
  have hpos : (0:ℝ) < 1 + u := by linarith
  have he : (0:ℝ) < Real.exp (-(u / 4)) := Real.exp_pos _
  have hkey : u ≤ (1 - Real.exp (-u)) * (1 + u) := (div_le_iff₀ hpos).mp (le_one_sub_exp hu)
  rw [div_le_div_iff₀ hd hu]
  nlinarith [mul_le_mul_of_nonneg_left hkey (le_of_lt he)]

/-- **The Lévy condition, pointwise.** -/
theorem min_mul_densityU_le {u : ℝ} (hu : 0 < u) :
    min 1 (u ^ 2) * densityU u ≤ 2 * Real.exp (-(u / 4)) := by
  have he : (0:ℝ) < Real.exp (-(u / 4)) := Real.exp_pos _
  have hdpos : 0 < densityU u := densityU_pos hu
  have hb := densityU_le hu
  rcases le_or_gt u 1 with h | h
  · have hmin : min 1 (u ^ 2) ≤ u ^ 2 := min_le_right _ _
    have h2 := mul_le_mul_of_nonneg_left hb (sq_nonneg u)
    have heq : u ^ 2 * ((1 + u) * Real.exp (-(u / 4)) / u)
        = u * (1 + u) * Real.exp (-(u / 4)) := by
      field_simp
    rw [heq] at h2
    have h3 : min 1 (u ^ 2) * densityU u ≤ u ^ 2 * densityU u :=
      mul_le_mul_of_nonneg_right hmin hdpos.le
    have h4 : u * (1 + u) * Real.exp (-(u / 4)) ≤ 2 * Real.exp (-(u / 4)) := by
      have hu2 : u * (1 + u) ≤ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hu2 he.le
    linarith
  · have hmin : min 1 (u ^ 2) ≤ 1 := min_le_left _ _
    have hstep : densityU u ≤ 2 * Real.exp (-(u / 4)) := by
      have h1u : (1 + u) / u ≤ 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      calc densityU u ≤ (1 + u) * Real.exp (-(u / 4)) / u := hb
        _ = ((1 + u) / u) * Real.exp (-(u / 4)) := by ring
        _ ≤ 2 * Real.exp (-(u / 4)) := mul_le_mul_of_nonneg_right h1u he.le
    have h3 : min 1 (u ^ 2) * densityU u ≤ 1 * densityU u :=
      mul_le_mul_of_nonneg_right hmin hdpos.le
    rw [one_mul] at h3
    linarith

theorem measurable_densityU : Measurable densityU := by
  unfold densityU; fun_prop

/-- **It is a Lévy measure.** -/
theorem integrableOn_min_mul_densityU :
    IntegrableOn (fun u => min 1 (u ^ 2) * densityU u) (Ioi (0:ℝ)) := by
  have hdom : IntegrableOn (fun u : ℝ => 2 * Real.exp (-(1/4) * u)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by norm_num : (0:ℝ) < 1/4)).const_mul 2
  refine Integrable.mono' hdom ?_ ?_
  · exact ((measurable_const.min (measurable_id.pow_const 2)).mul
      measurable_densityU).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun u hu => ?_
    have hu0 : (0:ℝ) < u := hu
    have hval := min_mul_densityU_le hu0
    have hnn : 0 ≤ min 1 (u ^ 2) * densityU u :=
      mul_nonneg (le_min zero_le_one (sq_nonneg u)) (densityU_pos hu0).le
    rw [Real.norm_of_nonneg hnn, show -(1/4) * u = -(u/4) by ring]
    exact hval

end Cvs.WeilForm.Archimedean.LevyMeasure

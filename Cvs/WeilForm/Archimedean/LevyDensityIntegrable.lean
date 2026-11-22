import Mathlib
import Cvs.WeilForm.Archimedean.LevyDensity

/-!
# The Lévy density is integrable away from the origin

    ∫_{u > δ} densityU < ∞   for every δ > 0

`densityU u = exp(−u/4)/(1 − exp(−u))` is bounded by a multiple of `exp(−u/4)` once `u` is
bounded away from `0`, where its denominator is bounded away from `0`.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real

namespace Cvs.WeilForm.Archimedean.LevyDensityIntegrable

/-- **The Lévy density is integrable on `(δ, ∞)`.** -/
theorem integrableOn_densityU {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn Cvs.WeilForm.Archimedean.LevyDensity.densityU (Set.Ioi δ) (volume : Measure ℝ) := by
  set C : ℝ := (1 - Real.exp (-δ))⁻¹ with hC
  have hden : 0 < 1 - Real.exp (-δ) := by
    have : Real.exp (-δ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hCpos : 0 < C := by rw [hC]; positivity
  -- the dominating function
  have hdom : Integrable (fun u : ℝ => C * Real.exp (-(1/4 : ℝ) * u))
      ((volume : Measure ℝ).restrict (Set.Ioi δ)) :=
    (exp_neg_integrableOn_Ioi δ (by norm_num : (0:ℝ) < 1/4)).const_mul C
  -- measurability on the half-line
  have hcont : ContinuousOn Cvs.WeilForm.Archimedean.LevyDensity.densityU (Set.Ioi δ) := by
    show ContinuousOn (fun u : ℝ => Real.exp (-(u / 4)) / (1 - Real.exp (-u))) (Set.Ioi δ)
    apply ContinuousOn.div₀
    · exact (Real.continuous_exp.comp (continuous_id.div_const 4).neg).continuousOn
    · exact (continuous_const.sub (Real.continuous_exp.comp continuous_id.neg)).continuousOn
    · intro u hu
      have hu0 : (0:ℝ) < u := lt_trans hδ hu
      have : Real.exp (-u) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
      linarith
  have hmeas : AEStronglyMeasurable Cvs.WeilForm.Archimedean.LevyDensity.densityU
      ((volume : Measure ℝ).restrict (Set.Ioi δ)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  refine hdom.mono' hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u hu => ?_)
  have hu0 : (0:ℝ) < u := lt_trans hδ hu
  have hpos : 0 < Cvs.WeilForm.Archimedean.LevyDensity.densityU u := Cvs.WeilForm.Archimedean.LevyDensity.densityU_pos hu0
  have hdenu : 1 - Real.exp (-δ) ≤ 1 - Real.exp (-u) := by
    have : Real.exp (-u) ≤ Real.exp (-δ) := Real.exp_le_exp.mpr (by have := Set.mem_Ioi.mp hu; linarith)
    linarith
  have hbound : Cvs.WeilForm.Archimedean.LevyDensity.densityU u ≤ C * Real.exp (-(1/4 : ℝ) * u) := by
    rw [Cvs.WeilForm.Archimedean.LevyDensity.densityU, hC]
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - Real.exp (-u))]
    have hexp : Real.exp (-(u / 4)) = Real.exp (-(1/4 : ℝ) * u) := by ring_nf
    rw [hexp, inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ hden]
    nlinarith [Real.exp_pos (-(1/4 : ℝ) * u), hdenu]
  rw [Real.norm_eq_abs, abs_of_pos hpos]
  exact hbound

end Cvs.WeilForm.Archimedean.LevyDensityIntegrable

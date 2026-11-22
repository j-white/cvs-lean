import Mathlib
import Cvs.WeilForm.Mollify.MollifyL2Contraction
import Cvs.WeilForm.Mollify.MollifyShiftedEnergy

/-!
# The mollified function is square integrable

    `f ∈ L²`, `ρ ≥ 0` continuous of compact support and unit mass  ⟹  `f ⋆ ρ ∈ L²`

the real-integral form of `Cvs.WeilForm.Mollify.MollifyL2Contraction`, which proved the bound before anything was known to be
finite.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real
open scoped ENNReal

namespace Cvs.WeilForm.Mollify.MollifiedL2

variable {f ρ : ℝ → ℝ}

/-- The mollification is measurable. -/
theorem measurable_conv (hfm : Measurable f) (hρm : Measurable ρ) :
    StronglyMeasurable (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ) := by
  have hprod : StronglyMeasurable
      (fun p : ℝ × ℝ => f (p.1 - p.2) * ρ p.2) :=
    ((hfm.comp (measurable_fst.sub measurable_snd)).mul
      (hρm.comp measurable_snd)).stronglyMeasurable
  exact hprod.integral_prod_right (ν := (volume : Measure ℝ))

/-- **The mollified function is in `L²`.** -/
theorem memLp_conv (hf : MemLp f 2 (volume : Measure ℝ)) (hfm : Measurable f)
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρm : Measurable ρ)
    (hρi : Integrable ρ (volume : Measure ℝ)) (hρnn : ∀ t, 0 ≤ ρ t)
    (hρ1 : (∫ t : ℝ, ρ t) = 1) :
    MemLp (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ) 2 (volume : Measure ℝ) := by
  have hmeas := measurable_conv hfm hρm
  rw [memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable]
  refine ⟨(hmeas.norm.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have henorm : (∫⁻ s : ℝ, ‖‖Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s‖ ^ 2‖ₑ)
      = ∫⁻ s : ℝ, ENNReal.ofReal ((∫ t : ℝ, f (s - t) * ρ t) ^ 2) := by
    refine lintegral_congr fun s => ?_
    rw [Real.enorm_eq_ofReal (by positivity), Real.norm_eq_abs, sq_abs]
    rfl
  rw [henorm]
  exact lt_of_le_of_lt
    (Cvs.WeilForm.Mollify.MollifyL2Contraction.lintegral_conv_sq_le hf hfm hρc hρs hρm hρi hρnn hρ1)
    ENNReal.ofReal_lt_top

end Cvs.WeilForm.Mollify.MollifiedL2

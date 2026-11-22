import Mathlib
import Cvs.Upstream.JensenProbabilityDensity
import Cvs.WeilForm.Mollify.MollifiedEnergy
import Cvs.WeilForm.Mollify.MollifiedSliceL2

/-!
# Mollification does not increase the L² norm

    ∫ (h ⋆ ρ)² ≤ ∫ h²      for `ρ ≥ 0` continuous of compact support and unit mass

`Cvs.Upstream.JensenProbabilityDensity` pointwise under the outer integral, `Cvs.WeilForm.Mollify.MollifiedEnergy` to evaluate the majorant.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real
open scoped ENNReal

namespace Cvs.WeilForm.Mollify.MollifyL2Contraction

variable {h ρ : ℝ → ℝ}

/-- Each slice of the majorant is integrable. -/
theorem integrable_slice_sq (hh : MemLp h 2 (volume : Measure ℝ)) (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρnn : ∀ t, 0 ≤ ρ t) (s : ℝ) :
    Integrable (fun t : ℝ => h (s - t) ^ 2 * ρ t) (volume : Measure ℝ) := by
  obtain ⟨C, hC⟩ := hρc.bounded_above_of_compact_support hρs
  have hrefl := Cvs.WeilForm.Mollify.MollifiedSliceL2.memLp_reflect_translate hh s
  refine (hrefl.integrable_sq.const_mul C).mono'
    ((hrefl.aestronglyMeasurable.pow 2).mul hρc.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t => ?_)
  have hρC : ρ t ≤ C := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC t)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hρnn t))]
  calc h (s - t) ^ 2 * ρ t ≤ h (s - t) ^ 2 * C :=
        mul_le_mul_of_nonneg_left hρC (sq_nonneg _)
    _ = C * h (s - t) ^ 2 := by ring

/-- **The mollified energy is bounded by the original.** -/
theorem lintegral_conv_sq_le (hh : MemLp h 2 (volume : Measure ℝ)) (hhm : Measurable h)
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρm : Measurable ρ)
    (hρi : Integrable ρ (volume : Measure ℝ)) (hρnn : ∀ t, 0 ≤ ρ t)
    (hρ1 : (∫ t : ℝ, ρ t) = 1) :
    (∫⁻ s : ℝ, ENNReal.ofReal ((∫ t : ℝ, h (s - t) * ρ t) ^ 2))
      ≤ ENNReal.ofReal (∫ s : ℝ, h s ^ 2) := by
  rw [← Cvs.WeilForm.Mollify.MollifiedEnergy.lintegral_double hh hhm hρm hρi hρnn hρ1]
  refine lintegral_mono fun s => ?_
  have hj := Cvs.Upstream.JensenProbabilityDensity.sq_integral_weighted_le hρnn hρi hρ1
    (Cvs.WeilForm.Mollify.MollifiedSliceL2.memLp_slice hh hρc hρs hρnn s)
  have hslice := integrable_slice_sq hh hρc hρs hρnn s
  rw [← ofReal_integral_eq_lintegral_ofReal hslice
    (Filter.Eventually.of_forall fun t => mul_nonneg (sq_nonneg _) (hρnn t))]
  exact ENNReal.ofReal_le_ofReal hj

end Cvs.WeilForm.Mollify.MollifyL2Contraction

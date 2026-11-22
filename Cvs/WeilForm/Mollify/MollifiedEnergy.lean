import Mathlib

/-!
# The mollified energy, evaluated

    ∫⁻ₛ ∫⁻ₜ h(s−t)²·ρ t  =  ∫ h²

Tonelli on a nonnegative kernel, then translation invariance inside and unit mass outside.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Function
open scoped ENNReal

namespace Cvs.WeilForm.Mollify.MollifiedEnergy

variable {h ρ : ℝ → ℝ}

/-- The kernel is measurable on the product. -/
theorem measurable_kernel (hh : Measurable h) (hρ : Measurable ρ) :
    Measurable (uncurry fun s t : ℝ => ENNReal.ofReal (h (s - t) ^ 2 * ρ t)) := by
  refine ENNReal.measurable_ofReal.comp ?_
  exact ((hh.comp (measurable_fst.sub measurable_snd)).pow_const 2).mul
    (hρ.comp measurable_snd)

/-- **The double integral collapses to the energy.** -/
theorem lintegral_double (hh : MemLp h 2 (volume : Measure ℝ)) (hhm : Measurable h)
    (hρm : Measurable ρ) (hρi : Integrable ρ (volume : Measure ℝ))
    (hρnn : ∀ t, 0 ≤ ρ t) (hρ1 : (∫ t : ℝ, ρ t) = 1) :
    (∫⁻ s : ℝ, ∫⁻ t : ℝ, ENNReal.ofReal (h (s - t) ^ 2 * ρ t))
      = ENNReal.ofReal (∫ s : ℝ, h s ^ 2) := by
  rw [lintegral_lintegral_swap (measurable_kernel hhm hρm).aemeasurable]
  -- the inner integral is the energy, shifted
  have hinner : ∀ t : ℝ, (∫⁻ s : ℝ, ENNReal.ofReal (h (s - t) ^ 2 * ρ t))
      = ENNReal.ofReal (ρ t) * ENNReal.ofReal (∫ s : ℝ, h s ^ 2) := by
    intro t
    have hfac : ∀ s : ℝ, ENNReal.ofReal (h (s - t) ^ 2 * ρ t)
        = ENNReal.ofReal (ρ t) * ENNReal.ofReal (h (s - t) ^ 2) := by
      intro s
      rw [← ENNReal.ofReal_mul (hρnn t)]
      congr 1
      ring
    simp only [hfac]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    have hshift : (∫⁻ s : ℝ, ENNReal.ofReal (h (s - t) ^ 2))
        = ∫⁻ s : ℝ, ENNReal.ofReal (h s ^ 2) := by
      have := lintegral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun s : ℝ => ENNReal.ofReal (h s ^ 2)) (-t)
      simpa [sub_eq_add_neg] using this
    rw [hshift, ← ofReal_integral_eq_lintegral_ofReal hh.integrable_sq
      (Filter.Eventually.of_forall fun s => sq_nonneg _)]
  simp only [hinner]
  rw [lintegral_mul_const' _ _ (by simp)]
  congr 1
  rw [← ofReal_integral_eq_lintegral_ofReal hρi (Filter.Eventually.of_forall hρnn), hρ1]
  simp

end Cvs.WeilForm.Mollify.MollifiedEnergy

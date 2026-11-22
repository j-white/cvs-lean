import Mathlib
import Cvs.WeilForm.Mollify.MollifiedL2
import Cvs.WeilForm.Mollify.MollifyShiftedEnergy

/-!
# The shifted energy decreases under mollification, as a real integral

    ∫ ((f⋆ρ)(s) − (f⋆ρ)(s+v))² ds  ≤  ∫ (f s − f (s+v))² ds

`Cvs.WeilForm.Mollify.MollifyShiftedEnergy` in `lintegral` form, read back now that `Cvs.WeilForm.Mollify.MollifiedL2` makes the left side finite.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real
open scoped ENNReal

namespace Cvs.WeilForm.Mollify.ShiftedEnergyReal

variable {f ρ : ℝ → ℝ}

/-- **The shifted energy decreases.** -/
theorem integral_shift_conv_le (hf : MemLp f 2 (volume : Measure ℝ)) (hfm : Measurable f)
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρm : Measurable ρ)
    (hρi : Integrable ρ (volume : Measure ℝ)) (hρnn : ∀ t, 0 ≤ ρ t)
    (hρ1 : (∫ t : ℝ, ρ t) = 1) (v : ℝ) :
    (∫ s : ℝ, (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s
        - Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ (s + v)) ^ 2)
      ≤ ∫ s : ℝ, (f s - f (s + v)) ^ 2 := by
  have hcm := Cvs.WeilForm.Mollify.MollifiedL2.memLp_conv hf hfm hρc hρs hρm hρi hρnn hρ1
  have hcv : MemLp (fun s : ℝ => Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ (s + v)) 2
      (volume : Measure ℝ) :=
    hcm.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) v)
  have hL : Integrable (fun s : ℝ => (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s
      - Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ (s + v)) ^ 2) (volume : Measure ℝ) :=
    (hcm.sub hcv).integrable_sq
  have hRnn : 0 ≤ ∫ s : ℝ, (f s - f (s + v)) ^ 2 :=
    integral_nonneg fun s => sq_nonneg _
  have hlint := Cvs.WeilForm.Mollify.MollifyShiftedEnergy.lintegral_shift_conv_le hf hfm hρc hρs hρm hρi hρnn hρ1 v
  rw [← ofReal_integral_eq_lintegral_ofReal hL
    (Filter.Eventually.of_forall fun s => sq_nonneg _)] at hlint
  exact (ENNReal.ofReal_le_ofReal_iff hRnn).mp hlint

end Cvs.WeilForm.Mollify.ShiftedEnergyReal

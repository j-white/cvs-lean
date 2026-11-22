import Mathlib
import Cvs.WeilForm.Mollify.MollifyLevyPointwise
import Cvs.WeilForm.Mollify.MollifyShiftedEnergy

/-!
# Mollification is a contraction of the `L²` distance

    ∫ ((f⋆ρ)(s) − (g⋆ρ)(s))² ds  ≤  ∫ (f s − g s)² ds

read off from the energy bound by linearity, which is what lets every limit in the composed
approximation be taken at the fixed target rather than along a moving one.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter

namespace Cvs.WeilForm.Mollify.MollifyDistanceContraction

variable {f g ρ : ℝ → ℝ}

/-- **Mollification is linear in its first argument.** -/
theorem conv_sub_conv (hf : MemLp f 2 (volume : Measure ℝ)) (hg : MemLp g 2 (volume : Measure ℝ))
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (s : ℝ) :
    Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s - Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv g ρ s
      = Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv (fun x => f x - g x) ρ s := by
  rw [Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv, Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv, Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv,
    ← integral_sub (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.integrable_slice hf hρc hρs s)
      (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.integrable_slice hg hρc hρs s)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)

/-- **Mollification contracts the `L²` distance.** -/
theorem integral_conv_sub_conv_le (hf : MemLp f 2 (volume : Measure ℝ))
    (hfm : Measurable f) (hg : MemLp g 2 (volume : Measure ℝ)) (hgm : Measurable g)
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρm : Measurable ρ)
    (hρi : Integrable ρ (volume : Measure ℝ)) (hρnn : ∀ t, 0 ≤ ρ t)
    (hρ1 : (∫ t : ℝ, ρ t) = 1) :
    (∫ s : ℝ, (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s - Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv g ρ s) ^ 2)
      ≤ ∫ s : ℝ, (f s - g s) ^ 2 := by
  have hd : MemLp (fun x => f x - g x) 2 (volume : Measure ℝ) := hf.sub hg
  have hdm : Measurable (fun x => f x - g x) := hfm.sub hgm
  have hkey := Cvs.WeilForm.Mollify.MollifyLevyPointwise.integral_conv_sq_le hd hdm hρc hρs hρm hρi hρnn hρ1
  have hrw : ∀ s : ℝ, (Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s
      - Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv g ρ s) ^ 2
      = Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv (fun x => f x - g x) ρ s ^ 2 := by
    intro s
    rw [conv_sub_conv hf hg hρc hρs s]
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw)]
  exact hkey

end Cvs.WeilForm.Mollify.MollifyDistanceContraction

import Mathlib
import Cvs.WeilForm.SelfConvolutionFunctional
import Cvs.Zeta.WeilPositivityStatement

/-!
# The archimedean channel decreases under mollification

    ∫_{u>0} densityU u · (g_{f⋆ρ}(0) − g_{f⋆ρ}(u/2))  ≤  the same for `f`

because each shifted energy does, and the Lévy density is nonnegative.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Cvs.Zeta.Explicit.Weil
open scoped ENNReal

namespace Cvs.WeilForm.Mollify.MollifyArchDecreases

variable {f ρ : ℝ → ℝ}

/-- The self-convolution deficit is half the shifted energy. -/
theorem deficit_eq {h : ℝ → ℝ} (hh : MemLp h 2 (volume : Measure ℝ)) (v : ℝ) :
    selfConvolution h 0 - selfConvolution h v
      = (∫ s : ℝ, (h s - h (s + v)) ^ 2) / 2 := by
  have hhv : MemLp (fun s : ℝ => h (s + v)) 2 (volume : Measure ℝ) :=
    hh.comp_measurePreserving (measurePreserving_add_right (volume : Measure ℝ) v)
  have hkey := Cvs.WeilForm.SelfConvolutionFunctional.integral_sq_sub_eq v hh.integrable_sq
    (hh.integrable_mul hhv)
  rw [hkey]
  ring

end Cvs.WeilForm.Mollify.MollifyArchDecreases

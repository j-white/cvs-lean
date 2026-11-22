import Mathlib
import Cvs.WeilForm.Mollify.MollifyShiftedEnergy
import Cvs.WeilForm.Mollify.MollifySupport

/-!
# The mollification stage

    weilForm P R (f⋆ρₙ) ≤ weilForm P R f + ε   eventually

for a window function with room at both ends and mollifiers whose radii tend to zero.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter

namespace Cvs.WeilForm.Mollify.MollificationStage

/-- **The mollification stays in the window when there is room for it.** -/
theorem support_conv_window {L a b δ : ℝ} (ha : 0 ≤ a - δ) (hb : b + δ ≤ L) {f ρ : ℝ → ℝ}
    (hfs : ∀ s ∉ Set.Ioc a b, f s = 0) (hρs : ∀ t : ℝ, δ < |t| → ρ t = 0) :
    ∀ s ∉ Set.Ioc (0:ℝ) L, Cvs.WeilForm.Mollify.MollifyShiftedEnergy.conv f ρ s = 0 := by
  intro s hs
  refine Cvs.WeilForm.Mollify.MollifySupport.conv_eq_zero_of_support hfs hρs ?_
  intro hmem
  simp only [Set.mem_Ioc] at hmem
  exact hs (Set.mem_Ioc.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩)

end Cvs.WeilForm.Mollify.MollificationStage

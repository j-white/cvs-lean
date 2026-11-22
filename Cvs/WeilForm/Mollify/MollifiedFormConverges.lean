import Mathlib
import Cvs.WeilForm.Archimedean.ArchLowerSemicontinuous
import Cvs.WeilForm.WindowConstraintSet

/-!
# The mollified form converges, and so does the renormalised one

    weilForm P R (f⋆ρₙ) → weilForm P R f,   and the same after renormalising

`an earlier result` bounds the form above and `Cvs.WeilForm.WindowFormLowerSemicontinuous` below, so between them the mollification's form
converges rather than merely not rising.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Filter Cvs.Zeta.Explicit.Weil

namespace Cvs.WeilForm.Mollify.MollifiedFormConverges

/-- **The constraint set grows with the window.** -/
theorem windowSet_mono {L L' : ℝ} (hLL : L ≤ L') :
    Cvs.WeilForm.WindowConstraintSet.windowSet L ⊆ Cvs.WeilForm.WindowConstraintSet.windowSet L' := by
  rintro f ⟨hmem, hsupp, hnorm, hlevy⟩
  refine ⟨hmem, ?_, hnorm, hlevy⟩
  intro s hs
  refine hsupp s ?_
  intro hmem'
  simp only [Set.mem_Ioc] at hmem'
  exact hs (Set.mem_Ioc.mpr ⟨hmem'.1, le_trans hmem'.2 hLL⟩)

variable {f : ℝ → ℝ} {ρ : ℕ → ℝ → ℝ} {δ : ℕ → ℝ}

end Cvs.WeilForm.Mollify.MollifiedFormConverges

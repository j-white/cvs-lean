import Mathlib

/-!
# The window's Weil form is continuous under dilation

    weilForm P R (f (·/a))  →  weilForm P R f     as `a → 1` from the positive side

for `f` in the window's constraint set, and the dilate is supported in `(0, aL]`, so a
dilation below `1` buys room at the right endpoint at a cost in the form that tends to zero.
-/

set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Real Set Filter

namespace Cvs.WeilForm.WeilFormDilationContinuous

/-- **The dilate is supported in the dilated window.** -/
theorem support_dilate {L a : ℝ} (ha : 0 < a) {f : ℝ → ℝ}
    (hsupp : ∀ s ∉ Set.Ioc (0:ℝ) L, f s = 0) :
    ∀ s ∉ Set.Ioc (0:ℝ) (a * L), f (s / a) = 0 := by
  intro s hs
  refine hsupp (s / a) ?_
  intro hmem
  simp only [Set.mem_Ioc] at hmem
  refine hs ?_
  simp only [Set.mem_Ioc]
  have hs0 : 0 < s := by
    have : 0 < a * (s / a) := mul_pos ha hmem.1
    rwa [mul_div_cancel₀ s ha.ne'] at this
  refine ⟨hs0, ?_⟩
  have : s / a ≤ L := hmem.2
  calc s = a * (s / a) := by field_simp
    _ ≤ a * L := by nlinarith [ha]

end Cvs.WeilForm.WeilFormDilationContinuous

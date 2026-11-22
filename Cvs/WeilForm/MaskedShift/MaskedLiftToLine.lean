import Mathlib
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.MasksCompose
import Cvs.Zeta.WeilPositivityStatement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory Real Cvs.Zeta.Explicit.Weil

namespace Cvs.PrimeOperator

open Cvs.Operator Cvs.Operator

/-!
# The lift to `ℝ`, and why the transfer needs no `β < 1`

`lift f` is `f` read through the `[0,1)` representative and extended by zero.
-/

/-- **ι.**  Extension by zero through the `[0,1)` representative. -/
noncomputable def lift (f : L2) : ℝ → ℝ :=
  (Set.Ico (0 : ℝ) 1).indicator fun y => (f : AddCircle (1 : ℝ) → ℝ) (y : AddCircle (1 : ℝ))

theorem lift_of_mem (f : L2) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    lift f y = (f : AddCircle (1 : ℝ) → ℝ) (y : AddCircle (1 : ℝ)) := by
  unfold lift
  rw [Set.indicator_of_mem (Set.mem_Ico.mpr ⟨hy0, hy1⟩)]

theorem lift_of_notMem (f : L2) {y : ℝ} (hy : y ∉ Set.Ico (0 : ℝ) 1) :
    lift f y = 0 := by
  unfold lift
  rw [Set.indicator_of_notMem hy]

/-- **N1e.**  In interval coordinates the forward mask is `y + β < 1`. -/
theorem mem_maskFwd_coe {β y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) :
    ((y : AddCircle (1 : ℝ)) ∈ maskFwd β) ↔ y + β < 1 := by
  simp only [maskFwd, Set.mem_ofPred_eq, rep_coe y hy0 hy1]

/-- **N3b.**  The self-convolution is even.  Needed because
`primePowerSideTruncated` symmetrises as `h u + h (-u)`. -/
theorem selfConvolution_neg (h : ℝ → ℝ) (t : ℝ) :
    selfConvolution h (-t) = selfConvolution h t := by
  unfold selfConvolution
  have hmp := measurePreserving_add_right (volume : Measure ℝ) (-t)
  have hcomp := hmp.integral_comp
    (MeasurableEquiv.addRight (-t)).measurableEmbedding (fun y => h y * h (y + t))
  rw [← hcomp]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  dsimp only
  rw [show x + -t + t = x by ring]
  ring

end Cvs.PrimeOperator

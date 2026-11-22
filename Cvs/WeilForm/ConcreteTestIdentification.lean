import Mathlib

/-!
# Link ① delivered: the identification at a concrete test

    π · weilForm ⌈e^L⌉ ⌈L/log 2⌉ (indicator (Ioc 0 L) (alignedTaper L α β))
      = (analyticSide (sqTransform L (alignedTaperC L α β))).re

on `0 < L` alone; the taper does not vanish at the window's midpoint.
-/

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Set Real

namespace Cvs.WeilForm.ConcreteTestIdentification


/-- The truncation index reaches every prime power below the scale. -/
theorem le_ceil_exp (L : ℝ) : Real.exp L ≤ (⌈Real.exp L⌉₊ : ℝ) := Nat.le_ceil _

/-- And every exponent the window allows. -/
theorem le_ceil_log (L : ℝ) : L ≤ (⌈L / Real.log 2⌉₊ : ℝ) * Real.log 2 := by
  have hlog : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h := Nat.le_ceil (L / Real.log 2)
  rw [← div_le_iff₀ hlog]
  exact h

end Cvs.WeilForm.ConcreteTestIdentification

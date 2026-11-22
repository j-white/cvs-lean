import Mathlib
import Cvs.WeilForm.MaskedShift.MaskedLiftToLine
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory Real

namespace Cvs.PrimeOperator

open Cvs.Operator Cvs.PrimeOperator

/-!
# The lift is square-integrable on the line

The self-convolution `∫ lift f · lift f (·+t)` needs its integrand integrable.
-/

/-- The two cuts of the fundamental domain give the same restricted measure:
`Ico 0 1` and `Ioc 0 1` differ by `{0, 1}`. -/
theorem restrict_Ico_eq_Ioc :
    (volume.restrict (Set.Ico (0:ℝ) 1)) = volume.restrict (Set.Ioc (0:ℝ) 1) :=
  Measure.restrict_congr_set (Ico_ae_eq_Icc.trans Ioc_ae_eq_Icc.symm)

/-- The covering map, with the interval normalised to `Ioc 0 1`. -/
theorem measurePreserving_mk' :
    MeasurePreserving (β := AddCircle (1:ℝ)) ((↑) : ℝ → AddCircle (1:ℝ))
      (volume.restrict (Set.Ioc (0:ℝ) 1)) volume := by
  have := AddCircle.measurePreserving_mk (1:ℝ) 0
  rwa [zero_add] at this

/-- Squaring commutes with the cut, since `0² = 0`. -/
theorem lift_sq (f : L2) :
    (fun y : ℝ => lift f y ^ 2)
      = (Set.Ico (0:ℝ) 1).indicator
          (fun y : ℝ => (f : AddCircle (1:ℝ) → ℝ) (y : AddCircle (1:ℝ)) ^ 2) := by
  funext y
  by_cases hy : y ∈ Set.Ico (0:ℝ) 1
  · rw [Set.indicator_of_mem hy, lift_of_mem f hy.1 hy.2]
  · rw [Set.indicator_of_notMem hy, lift_of_notMem f hy]
    ring

end Cvs.PrimeOperator

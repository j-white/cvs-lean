import Mathlib
import Cvs.WeilForm.MaskedShift.MaskedLiftSquareIntegrable
import Cvs.WeilForm.MaskedShift.MaskedLiftToLine
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory Real Cvs.Zeta.Explicit.Weil
open scoped InnerProductSpace NNReal ContDiff

namespace Cvs.PrimeOperator

open Cvs.Operator Cvs.PrimeOperator Cvs.PrimeOperator Cvs.PrimeOperator Cvs.PrimeOperator Cvs.PrimeOperator Cvs.PrimeOperator

/-!
# The operator bound, as an elementary inequality

Everything the development proves about the prime side can now be stated without mentioning an
operator, a circle, or a Hilbert space.
-/

variable {g : ℝ → ℝ}

/-- **The norm on the circle is the norm of the lift.**  `lift` is an isometry
onto its image: squaring commutes with the cut, and the fundamental domain
carries the whole integral. -/
theorem norm_sq_eq_integral_lift_sq (f : L2) : ‖f‖ ^ 2 = ∫ y : ℝ, lift f y ^ 2 := by
  have hinner : ⟪f, f⟫_ℝ = ‖f‖ ^ 2 := real_inner_self_eq_norm_sq f
  rw [← hinner, MeasureTheory.L2.inner_def]
  have h1 : (∫ z : T1, ⟪(f : T1 → ℝ) z, (f : T1 → ℝ) z⟫_ℝ)
      = ∫ z : T1, (f : T1 → ℝ) z ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp [sq]
  have h2 : (∫ z : T1, (f : T1 → ℝ) z ^ 2)
      = ∫ y in Set.Ioc (0:ℝ) 1, (f : T1 → ℝ) (y : T1) ^ 2 := by
    have h := AddCircle.integral_preimage (1:ℝ) 0 (fun z : T1 => (f : T1 → ℝ) z ^ 2)
    rw [zero_add] at h
    exact h.symm
  have h3 : (∫ y in Set.Ioc (0:ℝ) 1, (f : T1 → ℝ) (y : T1) ^ 2)
      = ∫ y in Set.Ico (0:ℝ) 1, (f : T1 → ℝ) (y : T1) ^ 2 := by
    rw [MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rw [show (∫ y in Set.Ico (0:ℝ) 1, (f : T1 → ℝ) (y : T1) ^ 2)
        = ∫ y in Set.Ioo (0:ℝ) 1, (f : T1 → ℝ) (y : T1) ^ 2 from
      integral_Ico_eq_integral_Ioo]
  rw [h1, h2, h3, ← integral_indicator measurableSet_Ico, ← lift_sq f]

end Cvs.PrimeOperator

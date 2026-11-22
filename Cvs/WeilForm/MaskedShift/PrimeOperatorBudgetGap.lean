import Mathlib
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition
import Cvs.WeilForm.MaskedShift.PrimeAtomRealisation
import Cvs.WeilForm.MaskedShift.PrimeSideAtomBudget

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory Real
open scoped InnerProductSpace NNReal ContDiff

namespace Cvs.PrimeOperator

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.PrimeOperator Cvs.PrimeOperator Cvs.PrimeOperator Cvs.PrimeOperator

/-!
# Where the budget gap lives

B46 bounds the prime side by `∑_q ‖A_q‖ · ‖f‖²`.
-/

variable {g : ℝ → ℝ}

/-- The prime side's operator: the sum of the atoms over the truncation. -/
noncomputable def primeOperator (c P R : ℕ) : L2 →L[ℝ] L2 :=
  ∑ p ∈ primeRange P, ∑ r ∈ Finset.Icc 1 R, atom c (p ^ r)

/-- Its quadratic form is the atom form. -/
theorem inner_primeOperator (c P R : ℕ) (f : L2) :
    ⟪primeOperator c P R f, f⟫_ℝ
      = ∑ p ∈ primeRange P, ∑ r ∈ Finset.Icc 1 R, ⟪atom c (p ^ r) f, f⟫_ℝ := by
  unfold primeOperator
  rw [_root_.sum_apply, sum_inner]
  exact Finset.sum_congr rfl fun p _ => by
    rw [_root_.sum_apply, sum_inner]

-- The triangle-inequality bound `‖primeOperator‖ ≤ atomBudget` is `Cvs.PrimeOperator`'s,
-- which needs only `1 < c`; the version that once stood here required every
-- prime power below the scale and is superseded.

end Cvs.PrimeOperator

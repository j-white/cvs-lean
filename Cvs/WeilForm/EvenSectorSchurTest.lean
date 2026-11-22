import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The even-sector Schur test on a symmetric family

On a symmetric family with even coefficients the form of any pair function equals the form of its
even-sector average `(A m n + A m (−n))/2`, and the pair `(i, neg i)` folds onto the diagonal; the
weighted Schur test with weights `1/|m|` then bounds the form below by twice the margins of the
positive modes, each margin a diagonal entry less `m` times a row sum over all `n ≥ 1`.
-/

noncomputable section

open Finset

namespace Cvs.WeilForm.EvenSectorSchurTest

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The even-sector average of a pair function over the sign of its second mode. -/
def evenPair (A : ℤ → ℤ → ℝ) (m n : ℤ) : ℝ := (A m n + A m (-n)) / 2

end Cvs.WeilForm.EvenSectorSchurTest

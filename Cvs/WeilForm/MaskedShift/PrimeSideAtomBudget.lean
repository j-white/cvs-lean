import Mathlib
import Cvs.WeilForm.MaskedShift.ChainArithmetic
import Cvs.WeilForm.MaskedShift.ChebFactorMonotone
import Cvs.WeilForm.MaskedShift.PrimeAtomRealisation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory Real
open scoped InnerProductSpace NNReal

namespace Cvs.PrimeOperator

open Cvs.Operator Cvs.WeilForm.MaskedShift.PrimeAtomRealisation Cvs.Operator

/-!
# The closed-form bound on the prime side

B45 turned the explicit formula's prime side into a sum of atom quadratic forms.
-/

/-- The index set of the truncated prime side. -/
def primeRange (P : ℕ) : Finset ℕ := (Finset.range (P + 1)).filter Nat.Prime

/-- The arithmetic bound: the summed atom norms. -/
noncomputable def atomBudget (c P R : ℕ) : ℝ :=
  ∑ p ∈ primeRange P, ∑ r ∈ Finset.Icc 1 R,
    Cvs.Operator.chebFactor (cap (Real.log c) (Real.log ((p ^ r : ℕ) : ℝ))) * wt (p ^ r)

end Cvs.PrimeOperator

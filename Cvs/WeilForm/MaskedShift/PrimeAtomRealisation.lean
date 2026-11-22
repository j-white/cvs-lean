import Mathlib
import Cvs.WeilForm.MaskedShift.CoherentFamilyDefs
import Cvs.WeilForm.MaskedShift.MaskedShiftComposition

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

open MeasureTheory ArithmeticFunction
open scoped NNReal

namespace Cvs.WeilForm.MaskedShift.PrimeAtomRealisation
open Cvs.Operator

open Cvs.Operator

/-!
# The arithmetic realisation

The prime atoms, defined as members of the coherent family of B20 rather than asserted to be.
-/

/-- The rotation number of a prime power at cutoff `c`, as a non-negative real. -/
noncomputable def rot (c q : ℕ) : ℝ≥0 := (Real.log q / Real.log c).toNNReal

/-- The arithmetic weight `Λ(q)/√q`. -/
noncomputable def wt (q : ℕ) : ℝ := vonMangoldt q / Real.sqrt q

theorem wt_nonneg (q : ℕ) : 0 ≤ wt q :=
  div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)

/-- **The prime atom**, as a member of the coherent family. -/
noncomputable def atom (c q : ℕ) : L2 →L[ℝ] L2 :=
  wt q • Cvs.Operator.W Snn (rot c q)

/-- The realisation, unfolded: the atom is the arithmetic weight times the
member of the coherent family at the arithmetic rotation number. -/
theorem atom_eq (c q : ℕ) : atom c q = wt q • Cvs.Operator.W Snn (rot c q) := rfl

/-! ## The abstract results, at the arithmetic parameters -/

end Cvs.WeilForm.MaskedShift.PrimeAtomRealisation

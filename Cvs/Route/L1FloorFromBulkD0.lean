import Mathlib
import Cvs.Approximant.SpineSubspace
import Cvs.StepA.StepAFromTwoGaps
import Cvs.WeilForm.EvenOddSplitForm
import Cvs.WeilForm.FormDomain
import Cvs.WeilForm.SymmetricBilinearForm
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# F3 at scale `x`, and L1's floor from F3 with the bulk and `D₀` floors

A floor `c_b` on `H ∩ Rᗮ`, a floor `d` on `R ≤ H` and the coupling `η` give `(η/2)min(c_b,d)` on `H`.
At `L = log x`: `D₀` is the span of the even parts of the rungs `j ≥ 2`, the normal is the even rung `1`
minus its `D₀`-projection, `H` the even classes orthogonal to it, and `F3 x η` the coupling of `QWbil`.
-/

noncomputable section

open Real Filter
open scoped InnerProductSpace

namespace Cvs.Route.L1FloorFromBulkD0

/-! ### The floor on `H` from a floor on `H ∩ Rᗮ`, a floor on `R` and the coupling -/

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

end General

/-! ### F3 at scale `x` -/

open Cvs.L2a.WindowChainInputsProlate (c0W)

/-- The scale-`x` window form domain, `L = log x`. -/
abbrev Dom (x : ℕ) := Cvs.WeilForm.FormDomain.formDomain (Real.log_natCast_nonneg x)

instance Dom.instNormedAddCommGroup (x : ℕ) : NormedAddCommGroup (Dom x) :=
  Submodule.normedAddCommGroup _

instance Dom.instInnerProductSpace (x : ℕ) : InnerProductSpace ℝ (Dom x) :=
  Submodule.innerProductSpace _

/-- The window Weil form at scale `x` as a bilinear form, `P = x`, `R = ⌈log₂ x⌉`. -/
def Bx (x : ℕ) : LinearMap.BilinForm ℝ (Dom x) :=
  Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)

/-- The even part of rung `j`: the even part of the `k_G` class of `h_{4j} − α_j h₀`. -/
def rung (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) : Dom x :=
  Cvs.WeilForm.EvenOddSplitForm.evenPart _ (Cvs.Approximant.SpineSubspace.spineMap x (Pi.single j 1))

/-- The rung indices `j ≥ 2`. -/
abbrev D0idx (x : ℕ) := {j : Cvs.Approximant.SpineSubspace.SF x // 2 ≤ (j : ℕ)}

/-- `D₀`: the span of the even rungs `j ≥ 2`. -/
def D0 (x : ℕ) : Submodule ℝ (Dom x) :=
  Submodule.span ℝ (Set.range fun j : D0idx x => rung x j.1)

instance D0.finiteDimensional (x : ℕ) : FiniteDimensional ℝ (D0 x) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

instance D0.hasOrthogonalProjection (x : ℕ) : (D0 x).HasOrthogonalProjection :=
  haveI : CompleteSpace (D0 x) := FiniteDimensional.complete ℝ _
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- The even rungs lie in the even classes. -/
theorem rung_mem_evenSub (x : ℕ) (j : Cvs.Approximant.SpineSubspace.SF x) :
    rung x j ∈ Cvs.StepA.StepAFromTwoGaps.evenSub (Real.log_natCast_nonneg x) :=
  Cvs.WeilForm.EvenOddSplitForm.reflD_evenPart _ _

end Cvs.Route.L1FloorFromBulkD0

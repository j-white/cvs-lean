import Mathlib
import Cvs.Route.L1FloorFromBulkD0
import Cvs.Route.WindowPositivityBulkCoupling
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
# The form coupling is a family of finite Schur complement bounds

For a symmetric `B` and `R = span r`, the coupling of `B` on the whole space against `R` holds iff it holds on
every finite-dimensional `H ≤ Rᗮ`, since the condition is pointwise in `w` and `w ∈ ℝ∙w`. In a finite family
`w₁, …, wₙ` of `Rᗮ` with Gram `G ≻ 0`, it is `XG⁻¹Xᵀ ≤ (1−δ)C` with `C = (B(rᵢ,rⱼ))`, `X = (B(rᵢ,wₖ))`; when
`B > 0` on `Rᗮ ∖ 0` (at scale `x`, `BulkFloor x b` with `b > 0`) these bounds are `FormCoupling x δ`.
-/

noncomputable section

namespace Cvs.WeilForm.CouplingFiniteSchur

open Matrix
open scoped MatrixOrder

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

end Generic

/-! ### At scale `x` -/

open Cvs.Route.L1FloorFromBulkD0 (Dom Bx)

theorem Bx_self (x : ℕ) (w : Dom x) : Bx x w w = Cvs.Route.WindowPositivityBulkCoupling.Qx x w := Cvs.WeilForm.SymmetricBilinearForm.QWbil_self _ _ _ _

end Cvs.WeilForm.CouplingFiniteSchur

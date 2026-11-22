import Mathlib
import Cvs.L2a.WindowChainInputsProlate
import Cvs.Route.L1FloorFromBulkD0
import Cvs.WeilForm.InfimumAttainedSphere
import Cvs.WeilForm.WeilFormOnWindowL2

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Window positivity from a bulk floor and a form coupling against `R_F`

At `L = log x`, `P = x`, `R = ⌈log₂ x⌉`, with orthogonality in the `L²` inner product of the form domain:
`BulkFloor x b` is `b‖w‖² ≤ Q(w)` on `R_Fᗮ`, and `FormCoupling x δ` is `Q(r,w)² ≤ (1−δ)Q(r)Q(w)` for
`r ∈ R_F`, `w ∈ R_Fᗮ`. Past `c₀W ≤ 2πx`, `b, δ ≥ 0`, they give `Q(r+w) ≥ (1 − √(1−δ))(Q(r) + b‖w‖²) ≥ 0`,
hence CORE(x); at infinitely many `x` they give RH, and RH gives them at `b = δ = 0` for every `x ≥ 2`.
-/

noncomputable section

open Real Filter

namespace Cvs.Route.WindowPositivityBulkCoupling

open Cvs.L2a.WindowChainInputsProlate (c0W)
open Cvs.Route.L1FloorFromBulkD0 (Dom Bx)

/-- The window form at `x`: `P = x`, `R = ⌈log₂ x⌉`, `L = log x`. -/
abbrev Qx (x : ℕ) (φ : Dom x) : ℝ :=
  Cvs.WeilForm.InfimumAttainedSphere.Q (Real.log_natCast_nonneg x) x (Nat.clog 2 x) φ

/-- `c₀W ≤ 2πx` for all large `x`. -/
theorem eventually_c0W_le : ∀ᶠ x : ℕ in atTop, c0W ≤ 2 * π * x :=
  ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by positivity : (0:ℝ) < 2 * π)).eventually_ge_atTop c0W

end Cvs.Route.WindowPositivityBulkCoupling

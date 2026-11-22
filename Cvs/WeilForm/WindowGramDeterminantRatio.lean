import Mathlib
import Cvs.Route.L1FloorFromBulkD0
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
# The determinant ratio of the window Gram and its pole-removed Gram

For `e : m → Dom x`, `f : n → Dom x`, the Gram matrices of `QWbil` and `M_x = QWbil − 2 Vc ⊗ Vc` on
`(e, f)` satisfy `G_Q = G_M + 2 vvᵀ`, `v = Vc ∘ (e, f)`; with `A = G_Q(e)`, `β = (Vc ∘ e)ᵀA⁻¹(Vc ∘ e)`:
`det G_M · det S(G_Q) = (1 − 2β) det S(G_M) det G_Q`, and for `2β > 1`,
`sign(det G_Q / det G_M) = −sign(det S(G_Q) / det S(G_M))`.
-/

noncomputable section

open Matrix

namespace Cvs.WeilForm.WindowGramDeterminantRatio

open Cvs.Route.L1FloorFromBulkD0 (Dom)

/-- The window form `QWbil` at `L = log x` and `R = ⌈log₂ x⌉`. -/
abbrev QW (x : ℕ) : LinearMap.BilinForm ℝ (Dom x) :=
  Cvs.WeilForm.SymmetricBilinearForm.QWbil (Real.log_natCast_nonneg x) x (Nat.clog 2 x)

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

end Cvs.WeilForm.WindowGramDeterminantRatio

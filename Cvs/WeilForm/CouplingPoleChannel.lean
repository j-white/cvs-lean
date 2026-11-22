import Mathlib
import Cvs.L2a.WindowFormTailLimit

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The pole channel of the form coupling

For `F` vanishing on `(−∞, 1]` in physical `L²` and `G` tame on `[α, β]`, Cauchy–Schwarz on the supports gives
`|P₋G| ≤ √(1/α − 1/β)‖G‖`, `|P₊G| ≤ √(β − α)‖G‖` and `|P₋F| ≤ ‖F‖`, so
`|P₊F·P₋G + P₋F·P₊G| ≤ (√(1/α − 1/β)|P₊F| + √(β − α)‖F‖)‖G‖`. At `[α, β] = [1/x, 1]` and `F = τ_a` this is
`|pole(τ_a, u)| ≤ (√(x − 1)|P₊τ_a| + √(1 − 1/x)‖τ_a‖)‖u‖`; the improper mean `P₊τ_a` stays as a symbol.
-/

noncomputable section

open Real Set MeasureTheory

namespace Cvs.WeilForm.CouplingPoleChannel

open Cvs.WeilForm.ThetaSpaceParseval (poleP poleM)
open Cvs.L2a.WindowFormTailLimit (Tame)

/-! ### Norms -/

/-- A tame test on `[α, β]` vanishes on `(−∞, 0]`. -/
theorem eq_zero_of_nonpos_of_tame {G : ℝ → ℝ} {α β : ℝ} (hG : Tame G α β) {θ : ℝ} (hθ : θ ≤ 0) :
    G θ = 0 :=
  hG.supp θ fun h => by linarith [hG.pos, h.1]

/-! ### The pole channel -/

/-! ### At scale `x` -/

end Cvs.WeilForm.CouplingPoleChannel

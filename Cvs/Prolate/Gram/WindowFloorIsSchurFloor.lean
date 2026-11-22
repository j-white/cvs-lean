import Mathlib
import Cvs.Prolate.EvenRungsByIndex
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RungCellGramDisplacement
import Cvs.Prolate.Gram.WindowFloorMinNormInterp

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The window floor `F_k` of (WF′) is the Schur floor of `RungCellGramDisplacement`'s cell Gram

`ProlateCellGramHalfUnit`'s cell Gram (the Gram of `√2 h_{4n}` in `L²(½, 1]`) and `RungCellGramDisplacement`'s `rungCellGram` are the same matrix, so `LayerFloorDeepRemainderB`'s
layer floor `F_k = λ_min(S_k)` is `SchurFloorIndexSet`'s Schur floor onto `{j ≥ k}`. Dual rows of the layer with Gram at most `c`
and `1/c` above the threshold `μ*C₀∞/2 + ε` therefore give (WF′).
-/

noncomputable section

open Real Filter Matrix

namespace Cvs.Prolate.Gram.WindowFloorIsSchurFloor
open Cvs.ZeroCounting

/-- **The two cell Grams agree**: `Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram x = Cvs.Prolate.Gram.RungCellGramDisplacement.rungCellGram x`. -/
theorem cellGram_eq_rungCellGram (x : ℕ) : Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram x = Cvs.Prolate.Gram.RungCellGramDisplacement.rungCellGram x := by
  ext n m
  rw [Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram_apply, Cvs.Prolate.Gram.RungCellGramDisplacement.rungCellGram, Cvs.Prolate.Gram.RungCellGramDisplacement.cellGram, of_apply,
    intervalIntegral.integral_of_le (by norm_num)]
  rfl

end Cvs.Prolate.Gram.WindowFloorIsSchurFloor

end

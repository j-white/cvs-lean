import Mathlib
import Cvs.Prolate.Gram.ProlateCellGramHalfUnit
import Cvs.Prolate.Gram.RungCellGramDisplacement
import Cvs.Prolate.Gram.WindowFloorIsSchurFloor

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The half-band floor of a layer block of the cell Gram

`G = 1 − C` is positive semidefinite. The half-band pair inequality on the layer block `A = {j ≥ k}`,
`aᵀG_AAa + (Λ^{1/2}a)ᵀG_AA(Λ^{1/2}a) ≤ κ|a|²`, gives `λ_min(C_AA) ≥ 1 − κ/(1 + λ_t)`, and with a far-loss bound `ℓ`
the layer floor `F_k ≥ 1 − κ/(1 + λ_t) − ℓ`.
-/

noncomputable section

open Real Set Matrix Finset Filter

namespace Cvs.Prolate.Gram.HalfBandLayerFloor
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.ProlateCellGramHalfUnit (cellGram lam lamTop)
open Cvs.Upstream.PencilLayerBound (IsFloor)

/-- `1 − C` is positive semidefinite at `80 ≤ 2πx`. -/
theorem one_sub_cellGram_posSemidef {x : ℕ} (hx : 80 ≤ 2 * π * x) : (1 - cellGram x).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun a => ?_
  · refine (isHermitian_one.sub ?_)
    ext n m
    simp [conjTranspose_apply, Cvs.Prolate.Gram.ProlateCellGramHalfUnit.cellGram_comm x m n]
  · have h := Cvs.Prolate.Gram.RungCellGramDisplacement.quad_rungCellGram_le hx a
    rw [← Cvs.Prolate.Gram.WindowFloorIsSchurFloor.cellGram_eq_rungCellGram] at h
    simp only [star_trivial, sub_mulVec, one_mulVec, dotProduct_sub]
    linarith

end Cvs.Prolate.Gram.HalfBandLayerFloor

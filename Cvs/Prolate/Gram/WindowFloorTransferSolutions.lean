import Mathlib
import Cvs.Prolate.Gram.EvenFirstCellEnergyGram
import Cvs.Prolate.Gram.RungCellGramDisplacement
import Cvs.Prolate.Gram.WindowFloorExtension
import Cvs.Prolate.Gram.WindowFloorMinNormInterp
import Cvs.Upstream.FourierTransferDualOperator

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# (WF′) from transfer solutions on `L²(0, 1/2] ⊕ L²(1/2, 1]`

The rungs `e_j = (√2 h_{4j}|_{(0,1/2]}, √2 h_{4j}|_{(1/2,1]})` are orthonormal in `E = L²(0, 1/2] ⊕ L²(1/2, 1]`,
`Q` is the projection on the first summand, and the cell parts `e_j − Qe_j` have Gram `rungCellGram x`. A symmetric
`F` fixing every rung and solutions `Φ_j = e_j + F(QΦ_j)` on the layer whose rows `Φ_j − QΦ_j` have Gram at most
`c` with `μ*C₀∞/2 + ε ≤ 1/c` give (WF′).
-/

noncomputable section

open Real Filter Matrix MeasureTheory

namespace Cvs.Prolate.Gram.WindowFloorTransferSolutions
open Cvs.ZeroCounting

open Cvs.Prolate.Gram.EvenFirstCellEnergyGram (L2c)
open Cvs.Prolate.Gram.RungCellGramDisplacement (rungCellGram rungCellGram_posDef)
open Cvs.Prolate.Gram.WindowFloorMinNormInterp (cellVec gram_cellVec)
open Cvs.Prolate.Gram.WindowFloorExtension (L2i innerVec orthonormal_pairs)
open Cvs.Upstream.FourierTransferDualOperator (IsSymmProj)

/-- The whole half-line `L²(0, 1/2] ⊕ L²(1/2, 1]`. -/
abbrev E2 : Type := WithLp 2 (L2i × L2c)

/-- The rung `e_j = (v_j, u_j)` in `E2`. -/
def rungE {x : ℕ} (hx : 80 ≤ 2 * π * x) (j : Fin x) : E2 := WithLp.toLp 2 (innerVec hx j, cellVec hx j)

/-- The projection `Q(a, b) = (a, 0)` on the inner summand. -/
def innerProj : E2 →ₗ[ℝ] E2 where
  toFun z := WithLp.toLp 2 ((WithLp.ofLp z).1, 0)
  map_add' z w := by
    rw [← WithLp.toLp_add]; congr 1; ext <;> simp
  map_smul' r z := by
    rw [RingHom.id_apply, ← WithLp.toLp_smul]; congr 1; ext <;> simp

/-- `Q(a, b) = (a, 0)`. -/
theorem innerProj_apply (z : E2) : innerProj z = WithLp.toLp 2 ((WithLp.ofLp z).1, 0) := rfl

/-- `Q` is a symmetric idempotent. -/
theorem isSymmProj_innerProj : IsSymmProj innerProj where
  idem z := rfl
  symm z w := by simp [innerProj_apply, WithLp.prod_inner_apply]

/-- The rungs are orthonormal in `E2`. -/
theorem inner_rungE {x : ℕ} (hx : 80 ≤ 2 * π * x) (a b : Fin x) :
    inner ℝ (rungE hx a) (rungE hx b) = if a = b then 1 else 0 := by
  rw [rungE, rungE, WithLp.prod_inner_apply]
  exact orthonormal_pairs hx a b

/-- The cell parts of the rungs have Gram `rungCellGram x`. -/
theorem gram_cellPart {x : ℕ} (hx : 80 ≤ 2 * π * x) :
    gram ℝ (fun b => rungE hx b - innerProj (rungE hx b)) = rungCellGram x := by
  rw [← gram_cellVec hx]
  ext a b
  simp [gram, rungE, innerProj_apply, WithLp.prod_inner_apply]

end Cvs.Prolate.Gram.WindowFloorTransferSolutions

end

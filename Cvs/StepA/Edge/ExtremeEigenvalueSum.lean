import Mathlib
import Cvs.StepA.Edge.DampedEdgeGram

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The edge discriminant as the sum of the extreme eigenvalues of `B(L)G`

For distinct positive ordinates the edge form is `pᵀB(L)p` in the pairing coordinates, the edge
supremum and infimum are the extreme eigenvalues of `M(L) = B(L)G` with `G` the Gram matrix of the
edge functions, so a vanishing edge discriminant makes `det(M ⊗ 1 + 1 ⊗ M)` vanish.
-/

noncomputable section

open Real MeasureTheory Filter Topology Matrix

namespace Cvs.StepA.Edge.ExtremeEigenvalueSum
open Cvs.ZeroCounting

open Cvs.StepA.Edge.TwoEdgeSplit (edgePair edgeForm)
open Cvs.StepA.Edge.EdgeDiscriminant (edgeRay edgeDisc)
open Cvs.StepA.Edge.DampedEdgeGram (edgeUnit pairVec pairVec_eq gramOn gram gram_comm gram_posDef comb continuous_comb pairVec_comb quad_gramOn bessel tendsto_gramOn tendsto_quad_gramOn quad_gramOn_le mergeOrd mergeW edgeDisc_merge pos_of_mem_mergeOrd nonempty_mergeOrd)

/-! ### Two generic facts of linear algebra -/

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive definite matrix inverts: `G G⁻¹ = 1`. -/
theorem mul_inv_of_posDef {G : Matrix n n ℝ} (hG : G.PosDef) : G * G⁻¹ = 1 :=
  mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hG.det_pos.ne')

end Generic

/-! ### The edge form in the pairing coordinates -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The extreme eigenvalues -/

omit [Fintype ι] [DecidableEq ι] in
/-- `G` is symmetric. -/
theorem gram_transpose (δ : ℝ) (g : ι → ℝ) : (gram δ g)ᵀ = gram δ g := by
  ext k l
  exact gram_comm δ g l k

/-! ### The complex edge operator -/

/-! ### Every finite family -/

end Cvs.StepA.Edge.ExtremeEigenvalueSum

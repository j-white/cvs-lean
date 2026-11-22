import Mathlib
import Cvs.Prolate.Gram.HalfCellGramHadamard
import Cvs.Upstream.CellFloorSandwichPosDef
import Cvs.Upstream.PencilLayerBound
import Cvs.Upstream.SchurLayerFloors

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The trace bound for a layer floor: `1/F_k ≤ Σ_{j ≥ k} (M⁻¹)_jj`

For `M ≻ 0` the Schur complement `S_k = ((M⁻¹)_{AA})⁻¹` onto `A = {j ≥ k}` has `λ_min(S_k) ≥ 1/tr((M⁻¹)_{AA})`,
because `uᵀPu ≤ tr(P)|u|²` for `P ⪰ 0`; so `1/F_k` is at most `Σ_{j ≥ k} 1/σ'_j` with `σ'_j = ((M⁻¹)_jj)⁻¹`.
-/

open Matrix Finset

namespace Cvs.Upstream.LayerFloorTraceBound

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The trace of the layer block of `M⁻¹` is the sum of the diagonal of `M⁻¹` over `{j ≥ k}`. -/
theorem trace_layerBlock (M : Matrix ι ι ℝ) (k : ι) :
    (M⁻¹.submatrix (Subtype.val : {j // k ≤ j} → ι) Subtype.val).trace
      = ∑ j ∈ univ.filter (k ≤ ·), M⁻¹ j j := by
  rw [Matrix.trace]
  exact (Finset.sum_subtype _ (fun j => by simp) fun j => M⁻¹ j j).symm

/-- **The trace bound**: `1/λ_min(S_k) ≤ Σ_{j ≥ k} (M⁻¹)_jj` for `M ≻ 0`. -/
theorem inv_layerFloor_le {M : Matrix ι ι ℝ} (hM : M.PosDef) (k : ι) :
    1 / Cvs.Upstream.PencilLayerBound.layerFloor hM k ≤ ∑ j ∈ univ.filter (k ≤ ·), M⁻¹ j j := by
  have hP : (M⁻¹.submatrix (Subtype.val : {j // k ≤ j} → ι) Subtype.val).PosDef :=
    hM.inv.submatrix Subtype.val_injective
  have htr : 0 < (M⁻¹.submatrix (Subtype.val : {j // k ≤ j} → ι) Subtype.val).trace := by
    have : Nonempty {j // k ≤ j} := ⟨⟨k, le_rfl⟩⟩
    rw [Matrix.trace]
    exact Finset.sum_pos (fun i _ => hP.diag_pos) Finset.univ_nonempty
  have hfl : Cvs.Upstream.PencilLayerBound.IsFloor (Cvs.Upstream.PencilLayerBound.layer M k)
      (1 / (M⁻¹.submatrix (Subtype.val : {j // k ≤ j} → ι) Subtype.val).trace) :=
    Cvs.Upstream.PencilLayerBound.isFloor_inv_of_quad_le hP htr fun u => Cvs.Prolate.Gram.HalfCellGramHadamard.quad_le_trace hP.posSemidef u
  have hle := (Cvs.Upstream.SchurLayerFloors.le_layerFloor_iff hM k _).2 hfl
  have hF := Cvs.Upstream.PencilLayerBound.layerFloor_pos hM k
  rw [← trace_layerBlock, div_le_iff₀ hF]
  rw [div_le_iff₀ htr] at hle
  linarith

/-- **In the cell-floor variables**: `1/F_k ≤ Σ_{j ≥ k} 1/σ'_j` with `σ'_j = ((M⁻¹)_jj)⁻¹`. -/
theorem inv_layerFloor_le_sum_sigmaP {M : Matrix ι ι ℝ} (hM : M.PosDef) (k : ι) :
    1 / Cvs.Upstream.PencilLayerBound.layerFloor hM k ≤ ∑ j ∈ univ.filter (k ≤ ·), 1 / Cvs.Upstream.CellFloorSandwichPosDef.sigmaP M j := by
  refine (inv_layerFloor_le hM k).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Cvs.Upstream.CellFloorSandwichPosDef.sigmaP, one_div, inv_inv]

end Cvs.Upstream.LayerFloorTraceBound

import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The twisted-pair floor of a layer

For `0 ≺ M ≼ 1` and a twist `d` with `d₀ ≤ d_j ≤ 1` on the layer `A = {j ≥ k}`, write `D′ = diag(d on A, 1 off A)`.
If `M + D′MD′` has the floor `1 − ε` on `A` in the variational sense, then `λ_min(S_A) ≥ ½ − ε/(2d₀)`.
At the bottom eigenvector `a` of `S_A` with its minimiser `v`, `Mv = λ_min(S_A)·a` on `A` and `0` off `A`, so
`(M + D′MD′)[v] ≤ 2λ_min(S_A)s + 1 − s` with `s = Σ d_j a_j²`.
-/

noncomputable section

open Matrix Finset

namespace Cvs.Upstream.TwistedPairLayerFloor


variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The coordinate embedding of the layer `{j ≥ k}` into `ι`. -/
def emb (k : ι) : Matrix ι {j // k ≤ j} ℝ := (1 : Matrix ι ι ℝ).submatrix id Subtype.val

/-- `(R u)_j = u_j` on the layer and `0` off it. -/
theorem emb_mulVec (k : ι) (u : {j // k ≤ j} → ℝ) (j : ι) :
    (emb k *ᵥ u) j = if h : k ≤ j then u ⟨j, h⟩ else 0 := by
  split_ifs with h
  · simp only [emb, mulVec, dotProduct, submatrix_apply, id_eq, Matrix.one_apply]
    rw [Finset.sum_eq_single ⟨j, h⟩]
    · simp
    · intro b _ hb; rw [ite_eq_right]; · simp
      intro e; exact hb (Subtype.ext e.symm)
    · simp
  · simp only [emb, mulVec, dotProduct, submatrix_apply, id_eq, Matrix.one_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [ite_eq_right]; · simp
    intro e; exact h (e ▸ b.2)

/-- `(Rᵀv)_a = v_a`. -/
theorem emb_transpose_mulVec (k : ι) (v : ι → ℝ) (a : {j // k ≤ j}) : ((emb k)ᵀ *ᵥ v) a = v a := by
  simp [emb, mulVec, dotProduct, transpose_apply, submatrix_apply, id_eq, Matrix.one_apply]

end Cvs.Upstream.TwistedPairLayerFloor

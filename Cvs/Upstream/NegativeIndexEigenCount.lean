import Mathlib
import Cvs.Upstream.NegativeSubspaceInertiaBound
import Cvs.Upstream.OnsetSchurCriterion

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The negative index counts eigenvalues: `n₋(M − BBᵀ) = #{eig(Bᵀ M⁻¹ B) > 1}`
For a real symmetric `A` and real `c`, the largest dimension of a subspace on which `c|y|² < yᵀAy`
(`y ≠ 0`) is the number of eigenvalues of `A` above `c`: `negIndex (c • 1 − A) = #{i | c < λᵢ}`.
With `Cvs.Upstream.OnsetSchurCriterion.negIndex_eq`, for `M` positive definite: `negIndex (M − BBᵀ) = #{i | 1 < λᵢ(Bᵀ M⁻¹ B)}`.
-/

noncomputable section

open Matrix Module

namespace Cvs.Upstream.NegativeIndexEigenCount

open Cvs.Upstream.OnsetSchurCriterion (NegDefOn negIndex)

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- The eigenvector matrix, as a real matrix. -/
abbrev U (hA : A.IsHermitian) : Matrix n n ℝ := (hA.eigenvectorUnitary : Matrix n n ℝ)

theorem star_U (hA : A.IsHermitian) : star (U hA) = (U hA)ᵀ := by
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

theorem U_mul_transpose (hA : A.IsHermitian) : U hA * (U hA)ᵀ = 1 := by
  rw [← star_U]; exact Unitary.coe_mul_star_self _

theorem transpose_mul_U (hA : A.IsHermitian) : (U hA)ᵀ * U hA = 1 := by
  rw [← star_U]; exact Unitary.coe_star_mul_self _

theorem A_eq (hA : A.IsHermitian) : A = U hA * diagonal hA.eigenvalues * (U hA)ᵀ := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [star_U, RCLike.ofReal_real_eq_id, Function.id_comp]

/-- **Spectral coordinates.** `yᵀAy = ∑ λᵢ zᵢ²` with `z = Uᵀy`. -/
theorem quad_eq (hA : A.IsHermitian) (y : n → ℝ) :
    y ⬝ᵥ (A *ᵥ y) = ∑ i, hA.eigenvalues i * ((U hA)ᵀ *ᵥ y) i ^ 2 := by
  conv_lhs => rw [A_eq hA]
  rw [← mulVec_mulVec, ← mulVec_mulVec, Cvs.Upstream.OnsetSchurCriterion.dot_mulVec_left, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_diagonal]; ring

/-- **Parseval.** `|y|² = ∑ zᵢ²` with `z = Uᵀy`. -/
theorem dot_self_eq (hA : A.IsHermitian) (y : n → ℝ) :
    y ⬝ᵥ y = ∑ i, ((U hA)ᵀ *ᵥ y) i ^ 2 := by
  conv_lhs => rw [show y = U hA *ᵥ ((U hA)ᵀ *ᵥ y) by
    rw [mulVec_mulVec, U_mul_transpose, one_mulVec]]
  rw [Cvs.Upstream.OnsetSchurCriterion.dot_mulVec_left, mulVec_mulVec, transpose_mul_U, one_mulVec,
    dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem quad_shift (hA : A.IsHermitian) (c : ℝ) (y : n → ℝ) :
    y ⬝ᵥ ((c • 1 - A) *ᵥ y) = ∑ i, (c - hA.eigenvalues i) * ((U hA)ᵀ *ᵥ y) i ^ 2 := by
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
    dot_self_eq hA, quad_eq hA, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Upper bound.** A negative definite subspace of `c • 1 − A` has dimension at most the number
of eigenvalues above `c`. -/
theorem finrank_le (hA : A.IsHermitian) (c : ℝ) {V : Submodule ℝ (n → ℝ)}
    (hV : NegDefOn (c • 1 - A) V) :
    finrank ℝ V ≤ Fintype.card {i // c < hA.eigenvalues i} := by
  refine Cvs.Upstream.NegativeSubspaceInertiaBound.finrank_le_card
    (fun i : {i // c < hA.eigenvalues i} => Cvs.Upstream.NegativeSubspaceInertiaBound.dotL (fun j => U hA j i))
    (fun y => y ⬝ᵥ ((c • 1 - A) *ᵥ y)) V ?_ hV
  intro y _ hker
  show 0 ≤ y ⬝ᵥ ((c • 1 - A) *ᵥ y)
  rw [quad_shift hA]
  refine Finset.sum_nonneg fun i _ => ?_
  by_cases hi : c < hA.eigenvalues i
  · have h0 : ((U hA)ᵀ *ᵥ y) i = 0 := by
      have := hker ⟨i, hi⟩
      simpa [Cvs.Upstream.NegativeSubspaceInertiaBound.dotL, mulVec, dotProduct, transpose_apply] using this
    rw [h0]; simp
  · exact mul_nonneg (by linarith [not_lt.mp hi]) (sq_nonneg _)

/-- Extension by zero from the coordinates above `c`. -/
def ext (hA : A.IsHermitian) (c : ℝ) (a : {i // c < hA.eigenvalues i} → ℝ) : n → ℝ :=
  fun j => if h : c < hA.eigenvalues j then a ⟨j, h⟩ else 0

/-- The span of the eigenvectors above `c`, as the image of `a ↦ U (ext a)`. -/
def upMap (hA : A.IsHermitian) (c : ℝ) : ({i // c < hA.eigenvalues i} → ℝ) →ₗ[ℝ] (n → ℝ) where
  toFun a := U hA *ᵥ ext hA c a
  map_add' a b := by
    rw [← mulVec_add]; congr 1; ext j; simp only [ext, Pi.add_apply]; split_ifs <;> simp
  map_smul' r a := by
    rw [RingHom.id_apply, ← mulVec_smul]; congr 1; ext j
    simp only [ext, Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

theorem coord_upMap (hA : A.IsHermitian) (c : ℝ) (a : {i // c < hA.eigenvalues i} → ℝ) :
    (U hA)ᵀ *ᵥ upMap hA c a = ext hA c a := by
  show (U hA)ᵀ *ᵥ (U hA *ᵥ ext hA c a) = _
  rw [mulVec_mulVec, transpose_mul_U, one_mulVec]

theorem upMap_injective (hA : A.IsHermitian) (c : ℝ) : Function.Injective (upMap hA c) := by
  intro a b h
  have := congrArg ((U hA)ᵀ *ᵥ ·) h
  simp only [coord_upMap] at this
  funext i
  have := congrFun this i
  simpa [ext, i.2] using this

/-- **Lower bound.** The span of the eigenvectors above `c` is negative definite for `c • 1 − A`. -/
theorem negDefOn_range (hA : A.IsHermitian) (c : ℝ) :
    NegDefOn (c • 1 - A) (LinearMap.range (upMap hA c)) := by
  rintro y ⟨a, rfl⟩ hy
  rw [quad_shift hA, coord_upMap]
  have ha : a ≠ 0 := fun h => hy (by rw [h, map_zero])
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  have hterm : ∀ j, (c - hA.eigenvalues j) * ext hA c a j ^ 2 ≤ 0 := fun j => by
    unfold ext
    split_ifs with h
    · exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
    · simp
  have hlt : (c - hA.eigenvalues i) * ext hA c a i ^ 2 < 0 := by
    simp only [ext, i.2, dite_true]
    exact mul_neg_of_neg_of_pos (by linarith [i.2]) (sq_pos_of_ne_zero hi)
  calc ∑ j, (c - hA.eigenvalues j) * ext hA c a j ^ 2
      < ∑ j, (0 : ℝ) := Finset.sum_lt_sum (fun j _ => hterm j) ⟨i, Finset.mem_univ _, hlt⟩
    _ = 0 := by simp

/-- **The negative index counts eigenvalues above `c`.** -/
theorem negIndex_smul_one_sub (hA : A.IsHermitian) (c : ℝ) :
    negIndex (c • 1 - A) = Fintype.card {i // c < hA.eigenvalues i} := by
  refine IsGreatest.csSup_eq ⟨⟨_, negDefOn_range hA c, ?_⟩, ?_⟩
  · rw [LinearMap.finrank_range_of_inj (upMap_injective hA c), Module.finrank_fintype_fun_eq_card]
  · rintro d ⟨V, hV, rfl⟩
    exact finrank_le hA c hV

end Cvs.Upstream.NegativeIndexEigenCount

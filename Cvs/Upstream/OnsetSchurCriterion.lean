import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The onset criterion: negative directions of `M − B Bᵀ` are those of `1 − Bᵀ M⁻¹ B`
For `M` positive definite and any `B`, `x ↦ Bᵀx` carries a negative definite subspace of
`M − B Bᵀ` injectively onto one of `1 − Bᵀ M⁻¹ B`, and `y ↦ M⁻¹ B y` carries back; the two maximal
dimensions agree. For one column `b`: `M − c² b bᵀ` has a negative direction iff
`1 < c² bᵀ M⁻¹ b`, iff `wᵀ M w < c²` for some `w` with `b ⬝ w = 1`; `min {wᵀMw : b ⬝ w = 1} = 1/(bᵀM⁻¹b)`.
-/

noncomputable section

open Matrix Module

namespace Cvs.Upstream.OnsetSchurCriterion

variable {n κ : Type*} [Fintype n] [DecidableEq n] [Fintype κ]

/-- `xᵀ A x < 0` for every nonzero `x ∈ V`. -/
def NegDefOn {m : Type*} [Fintype m] (A : Matrix m m ℝ) (V : Submodule ℝ (m → ℝ)) : Prop :=
  ∀ x ∈ V, x ≠ 0 → x ⬝ᵥ (A *ᵥ x) < 0

/-- The negative index: the largest dimension of a negative definite subspace. -/
def negIndex {m : Type*} [Fintype m] (A : Matrix m m ℝ) : ℕ :=
  sSup {d | ∃ V : Submodule ℝ (m → ℝ), NegDefOn A V ∧ finrank ℝ V = d}

theorem dot_mulVec_comm {m : Type*} [Fintype m] {A : Matrix m m ℝ} (hA : Aᵀ = A) (x z : m → ℝ) :
    x ⬝ᵥ (A *ᵥ z) = z ⬝ᵥ (A *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]

theorem transpose_eq_of_posSemidef {m : Type*} [Fintype m] {A : Matrix m m ℝ}
    (hA : A.PosSemidef) : Aᵀ = A := by
  have := hA.1
  rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this

theorem quad_nonneg {m : Type*} [Fintype m] {A : Matrix m m ℝ} (hA : A.PosSemidef) (x : m → ℝ) :
    0 ≤ x ⬝ᵥ (A *ᵥ x) := by
  simpa using hA.dotProduct_mulVec_nonneg x

/-- **Cauchy–Schwarz for a positive semidefinite form.** -/
theorem sq_le_mul {m : Type*} [Fintype m] {A : Matrix m m ℝ} (hA : A.PosSemidef) (x z : m → ℝ) :
    (x ⬝ᵥ (A *ᵥ z)) ^ 2 ≤ (x ⬝ᵥ (A *ᵥ x)) * (z ⬝ᵥ (A *ᵥ z)) := by
  have hsym := dot_mulVec_comm (transpose_eq_of_posSemidef hA)
  have h : ∀ t : ℝ, 0 ≤ (z ⬝ᵥ (A *ᵥ z)) * (t * t) + 2 * (x ⬝ᵥ (A *ᵥ z)) * t
      + x ⬝ᵥ (A *ᵥ x) := by
    intro t
    have := quad_nonneg hA (x + t • z)
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul] at this
    rw [hsym z x] at this
    nlinarith [this]
  have := discrim_le_zero h
  unfold discrim at this
  nlinarith [this]

omit [DecidableEq n] in
theorem dot_mulVec_left {m : Type*} [Fintype m] (B : Matrix n m ℝ) (x : n → ℝ) (z : m → ℝ) :
    x ⬝ᵥ (B *ᵥ z) = (Bᵀ *ᵥ x) ⬝ᵥ z := by
  rw [dotProduct_mulVec, mulVec_transpose]

end Cvs.Upstream.OnsetSchurCriterion

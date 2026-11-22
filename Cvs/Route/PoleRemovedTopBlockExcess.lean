import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# One negative direction of the pole-removed top block bounds the pole excess below

For `A ≻ 0` over `ℝ`: `(b·a)² ≤ (aᵀAa)(bᵀA⁻¹b)`. Hence for `Q` on `m ⊕ n` with `A = Q₁₁ ≻ 0`, `t ≥ 0`,
`v = (b, c)`, `q = aᵀAa > 0`: `(t (b·a)² − q)/q ≤ D = tβ − 1`; `aᵀ(Q − t vvᵀ)₁₁a < 0` gives `D > 0`, and
conversely `D > 0` is witnessed by `a = A⁻¹b`, so `D > 0` iff `(Q − t vvᵀ)₁₁` has a negative direction.
-/

noncomputable section

open Matrix

namespace Cvs.Route.PoleRemovedTopBlockExcess


variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Cauchy–Schwarz against the inverse**: for `A ≻ 0`, `(b·a)² ≤ (aᵀAa)(bᵀA⁻¹b)`. -/
theorem sq_dotProduct_le_mul_inv {A : Matrix m m ℝ} (hA : A.PosDef) (a b : m → ℝ) :
    (b ⬝ᵥ a) ^ 2 ≤ (a ⬝ᵥ (A *ᵥ a)) * (b ⬝ᵥ (A⁻¹ *ᵥ b)) := by
  have hAu : IsUnit A.det := (isUnit_iff_isUnit_det _).mp hA.isUnit
  set z := A⁻¹ *ᵥ b with hz
  have hAz : A *ᵥ z = b := by rw [hz, mulVec_mulVec, mul_nonsing_inv _ hAu, one_mulVec]
  have hAt : Aᵀ = A := by simpa [conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have hza : z ⬝ᵥ (A *ᵥ a) = b ⬝ᵥ a := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hAt, hAz, dotProduct_comm]
  have hzz : z ⬝ᵥ (A *ᵥ z) = b ⬝ᵥ z := by rw [hAz, dotProduct_comm]
  have haz : a ⬝ᵥ (A *ᵥ z) = b ⬝ᵥ a := by rw [hAz, dotProduct_comm]
  have hq : ∀ l : ℝ, 0 ≤ (a ⬝ᵥ (A *ᵥ a)) * (l * l) + (-2 * (b ⬝ᵥ a)) * l + b ⬝ᵥ z := by
    intro l
    have hp := hA.posSemidef.dotProduct_mulVec_nonneg (z - l • a)
    rw [star_trivial] at hp
    simp only [mulVec_sub, mulVec_smul, dotProduct_sub, sub_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, hza, hzz, haz] at hp
    nlinarith
  have := discrim_le_zero hq
  rw [discrim] at this
  nlinarith

end Cvs.Route.PoleRemovedTopBlockExcess

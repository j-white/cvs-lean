import Mathlib
import Cvs.Upstream.MergedBoundSchurForm

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The form-metric coupling in Gram form and as a top eigenvalue

For `R = span{rᵢ}` with Gram `C = (B(rᵢ,rⱼ))`, `Coupling B H R η` is `(Σᵢ aᵢB(rᵢ,w))² ≤ (1−η)(aᵀCa)B(w,w)`.
With `vᵢ ∈ H ∩ Rᗮ` representing `B(rᵢ,·)` there and `G = (B(vᵢ,vⱼ))`, it is `G ≤ (1−η)C`, and for any
`S` with `SᵀCS = 1` it is `λ(SᵀGS) ≤ 1−η` for every eigenvalue.
-/

noncomputable section

namespace Cvs.WeilForm.CouplingGramTopEigen

open Matrix
open scoped InnerProductSpace MatrixOrder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι]

/-! ### Representing vectors -/

/-- **Cauchy–Schwarz** for a symmetric form that is nonnegative on a subspace `K`. -/
theorem sq_le_mul_of_nonneg {B : LinearMap.BilinForm ℝ E} (hB : B.IsSymm) {K : Submodule ℝ E}
    (hK : ∀ w ∈ K, 0 ≤ B w w) {u w : E} (hu : u ∈ K) (hw : w ∈ K) :
    B u w ^ 2 ≤ B u u * B w w := by
  have hq : ∀ s : ℝ, 0 ≤ B u u * (s * s) + (2 * B u w) * s + B w w := by
    intro s
    have h := hK (s • u + w) (K.add_mem (K.smul_mem s hu) hw)
    rw [Cvs.Upstream.MergedBoundSchurForm.apply_smul_add hB] at h
    nlinarith
  have hd := discrim_le_zero hq
  rw [discrim] at hd
  nlinarith

/-- `SᵀGS` is symmetric when `G` is. -/
theorem isHermitian_whitened {G : Matrix ι ι ℝ} (hG : G.IsHermitian) (S : Matrix ι ι ℝ) :
    (Sᵀ * G * S).IsHermitian := by
  unfold IsHermitian at hG ⊢
  simp only [conjTranspose_eq_transpose_of_trivial] at hG ⊢
  rw [transpose_mul, transpose_mul, transpose_transpose, hG, mul_assoc]

/-- `S = C^{−1/2}` (`CFC.sqrt C⁻¹`) whitens a positive definite `C`: `SᵀCS = 1`. -/
theorem invSqrt_whitens [DecidableEq ι] {C : Matrix ι ι ℝ} (hC : C.PosDef) :
    (CFC.sqrt C⁻¹)ᵀ * C * CFC.sqrt C⁻¹ = 1 := by
  set S := CFC.sqrt C⁻¹ with hSd
  have hS0 : 0 ≤ S := CFC.sqrt_nonneg _
  have hT : Sᵀ = S := by
    have h := (Matrix.nonneg_iff_posSemidef.mp hS0).isHermitian
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hSS : S * S = C⁻¹ := CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr hC.inv.posSemidef)
  have hCu : IsUnit C.det := (Matrix.isUnit_iff_isUnit_det C).mp hC.isUnit
  have h1 : S * (S * C) = 1 := by rw [← mul_assoc, hSS, Matrix.nonsing_inv_mul _ hCu]
  rw [hT, mul_eq_one_comm.mp h1]

/-! ### A `B`-orthonormal frame of `H ∩ Rᗮ` -/

section Frame

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

end Frame

end Cvs.WeilForm.CouplingGramTopEigen

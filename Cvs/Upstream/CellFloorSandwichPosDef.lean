import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The cell-floor sandwich for a positive definite Gram matrix

For `M ≻ 0` put `σ'_t = ((M⁻¹)_tt)⁻¹ = min{bᵀMb : b_t = 1}`. Then `ω_t/σ'_t ≤ C` for every admissible
`Σ ω_j b_j² ≤ C bᵀMb`, and `C = Σ_j ω_j/σ'_j` is admissible; blockwise, `b_Tᵀ((M⁻¹)_TT)⁻¹b_T ≤ bᵀMb`, so
pencil bounds `c_k` on a partition sum. For a Gram matrix with `v_t ∈ s h + W`, `v_j ∈ W`: `s² dist(h, W)² ≤ σ'_t`.
-/

noncomputable section

open Matrix

namespace Cvs.Upstream.CellFloorSandwichPosDef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The cell floor `σ'_t = ((M⁻¹)_tt)⁻¹`. -/
def sigmaP (M : Matrix ι ι ℝ) (t : ι) : ℝ := (M⁻¹ t t)⁻¹

omit [Fintype ι] [DecidableEq ι] in
/-- A real positive semidefinite matrix is symmetric. -/
theorem transpose_eq_of_posSemidef {M : Matrix ι ι ℝ} (hM : M.PosSemidef) : Mᵀ = M := by
  simpa [conjTranspose_eq_transpose_of_trivial] using hM.isHermitian.eq

omit [DecidableEq ι] in
/-- Completing the square: `2 (Mu)·b − uᵀMu ≤ bᵀMb` for `M ⪰ 0`. -/
theorem two_mul_dot_sub_le {M : Matrix ι ι ℝ} (hM : M.PosSemidef) (u b : ι → ℝ) :
    2 * ((M *ᵥ u) ⬝ᵥ b) - u ⬝ᵥ (M *ᵥ u) ≤ b ⬝ᵥ (M *ᵥ b) := by
  have h := hM.dotProduct_mulVec_nonneg (b - u)
  rw [star_trivial] at h
  have hs : u ⬝ᵥ (M *ᵥ b) = (M *ᵥ u) ⬝ᵥ b := by
    rw [dotProduct_mulVec, ← mulVec_transpose, transpose_eq_of_posSemidef hM]
  simp only [mulVec_sub, dotProduct_sub, sub_dotProduct] at h
  rw [hs, dotProduct_comm b (M *ᵥ u)] at h
  linarith

/-- The dual form: `2 z·b − zᵀM⁻¹z ≤ bᵀMb` for `M ≻ 0`. -/
theorem two_mul_dot_sub_inv_le {M : Matrix ι ι ℝ} (hM : M.PosDef) (z b : ι → ℝ) :
    2 * (z ⬝ᵥ b) - (M⁻¹ *ᵥ z) ⬝ᵥ z ≤ b ⬝ᵥ (M *ᵥ b) := by
  have hu : IsUnit M.det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  have hMz : M *ᵥ (M⁻¹ *ᵥ z) = z := by rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have h := two_mul_dot_sub_le hM.posSemidef (M⁻¹ *ᵥ z) b
  rw [hMz] at h
  linarith [dotProduct_comm (M⁻¹ *ᵥ z) z]

/-- Each squared coefficient is controlled by the cell floor: `b_t² σ'_t ≤ bᵀMb`. -/
theorem coef_sq_mul_le {M : Matrix ι ι ℝ} (hM : M.PosDef) (b : ι → ℝ) (t : ι) :
    b t ^ 2 * sigmaP M t ≤ b ⬝ᵥ (M *ᵥ b) := by
  have hp : 0 < M⁻¹ t t := hM.inv.diag_pos
  set s := b t / M⁻¹ t t
  have h := two_mul_dot_sub_inv_le hM (s • Pi.single t 1) b
  have h1 : (s • Pi.single t (1 : ℝ)) ⬝ᵥ b = s * b t := by simp
  have h2 : (M⁻¹ *ᵥ (s • Pi.single t (1 : ℝ))) ⬝ᵥ (s • Pi.single t 1) = s ^ 2 * M⁻¹ t t := by
    simp [mulVec_smul, sq]; ring
  rw [h1, h2] at h
  have : b t ^ 2 * sigmaP M t = 2 * (s * b t) - s ^ 2 * M⁻¹ t t := by
    simp only [sigmaP, s]; field_simp; ring
  linarith

/-- The cell floor is positive. -/
theorem sigmaP_pos {M : Matrix ι ι ℝ} (hM : M.PosDef) (t : ι) : 0 < sigmaP M t :=
  inv_pos.mpr hM.inv.diag_pos

/-- The minimiser `b* = σ'_t M⁻¹e_t` of `bᵀMb` on `b_t = 1`. -/
def argminP (M : Matrix ι ι ℝ) (t : ι) : ι → ℝ := sigmaP M t • (M⁻¹ *ᵥ Pi.single t 1)

/-- The minimiser has unit `t`-coefficient. -/
theorem argminP_apply_self {M : Matrix ι ι ℝ} (hM : M.PosDef) (t : ι) : argminP M t t = 1 := by
  have hp : 0 < M⁻¹ t t := hM.inv.diag_pos
  simp [argminP, sigmaP, hp.ne']

/-- The minimiser attains the cell floor: `b*ᵀMb* = σ'_t`. -/
theorem quad_argminP {M : Matrix ι ι ℝ} (hM : M.PosDef) (t : ι) :
    argminP M t ⬝ᵥ (M *ᵥ argminP M t) = sigmaP M t := by
  have hp : 0 < M⁻¹ t t := hM.inv.diag_pos
  have hu : IsUnit M.det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  have hMz : M *ᵥ (M⁻¹ *ᵥ Pi.single t (1 : ℝ)) = Pi.single t 1 := by
    rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  simp only [argminP, mulVec_smul, hMz, dotProduct_smul, dotProduct_single, mul_one,
    smul_eq_mul]
  simp only [mulVec_single_one, sigmaP]
  simp [hp.ne']

/-- Schur complement: `σ'_t = ((M⁻¹)_tt)⁻¹` is the least value of `bᵀMb` on `b_t = 1`. -/
theorem isLeast_sigmaP {M : Matrix ι ι ℝ} (hM : M.PosDef) (t : ι) :
    IsLeast {q | ∃ b : ι → ℝ, b t = 1 ∧ b ⬝ᵥ (M *ᵥ b) = q} (sigmaP M t) := by
  refine ⟨⟨argminP M t, argminP_apply_self hM t, quad_argminP hM t⟩, ?_⟩
  rintro _ ⟨b, hb, rfl⟩
  simpa [hb] using coef_sq_mul_le hM b t

/-- P5: `Σ_j ω_j b_j² ≤ (Σ_j ω_j/σ'_j) bᵀMb` for `ω ≥ 0`. -/
theorem sum_weight_le {M : Matrix ι ι ℝ} (hM : M.PosDef) {ω : ι → ℝ} (hω : ∀ j, 0 ≤ ω j) (b : ι → ℝ) :
    ∑ j, ω j * b j ^ 2 ≤ (∑ j, ω j / sigmaP M j) * b ⬝ᵥ (M *ᵥ b) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have h := coef_sq_mul_le hM b j
  have hs := sigmaP_pos hM j
  rw [div_mul_eq_mul_div, le_div_iff₀ hs, mul_assoc]
  exact mul_le_mul_of_nonneg_left h (hω j)

/-- The block floor: `b_Tᵀ((M⁻¹)_TT)⁻¹ b_T ≤ bᵀMb` for an injective block `g : κ → ι`. -/
theorem block_quad_le {κ : Type*} [Fintype κ] [DecidableEq κ] {M : Matrix ι ι ℝ} (hM : M.PosDef)
    {g : κ → ι} (hg : Function.Injective g) (b : ι → ℝ) :
    (b ∘ g) ⬝ᵥ ((M⁻¹.submatrix g g)⁻¹ *ᵥ (b ∘ g)) ≤ b ⬝ᵥ (M *ᵥ b) := by
  set P := M⁻¹.submatrix g g
  have hP : P.PosDef := hM.inv.submatrix hg
  have hPu : IsUnit P.det := (isUnit_iff_isUnit_det _).mp hP.isUnit
  set R : Matrix ι κ ℝ := (1 : Matrix ι ι ℝ).submatrix id g
  set v := b ∘ g
  have hRb : b ᵥ* R = v := by
    ext k; simp [R, v, vecMul, dotProduct, Matrix.one_apply]
  have hRMR : Rᵀ * M⁻¹ * R = P := by
    ext k l; simp [R, P, Matrix.mul_apply, Matrix.one_apply]
  have key : ∀ y : κ → ℝ, (M⁻¹ *ᵥ (R *ᵥ y)) ⬝ᵥ (R *ᵥ y) = y ⬝ᵥ (P *ᵥ y) := by
    intro y
    rw [← hRMR, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec y Rᵀ, vecMul_transpose,
      dotProduct_comm]
  have h := two_mul_dot_sub_inv_le hM (R *ᵥ (P⁻¹ *ᵥ v)) b
  have h1 : (R *ᵥ (P⁻¹ *ᵥ v)) ⬝ᵥ b = v ⬝ᵥ (P⁻¹ *ᵥ v) := by
    rw [dotProduct_comm, dotProduct_mulVec, hRb]
  have h2 : (M⁻¹ *ᵥ (R *ᵥ (P⁻¹ *ᵥ v))) ⬝ᵥ (R *ᵥ (P⁻¹ *ᵥ v)) = v ⬝ᵥ (P⁻¹ *ᵥ v) := by
    rw [key, mulVec_mulVec, mul_nonsing_inv _ hPu, one_mulVec, dotProduct_comm]
  rw [h1, h2] at h
  linarith

section Gram

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq ι] in
/-- The Gram form is the squared norm of the combination: `bᵀ(gram v)b = ‖Σ_j b_j v_j‖²`. -/
theorem quad_gram (v : ι → E) (b : ι → ℝ) :
    b ⬝ᵥ (gram ℝ v *ᵥ b) = ‖∑ j, b j • v j‖ ^ 2 := by
  have h := star_dotProduct_gram_mulVec (𝕜 := ℝ) v b b
  rw [star_trivial] at h
  rw [h, real_inner_self_eq_norm_sq]

end Gram

end Cvs.Upstream.CellFloorSandwichPosDef

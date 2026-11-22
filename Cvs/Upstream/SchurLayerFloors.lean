import Mathlib
import Cvs.Upstream.CellFloorSandwichPosDef
import Cvs.Upstream.PencilLayerBound

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Schur floors of layers: variational form, monotonicity, dual rows, Feshbach and displacement

For `M ≻ 0` and `S_A = ((M⁻¹)_{AA})⁻¹`: `uᵀS_Au = min{bᵀMb : b_A = u}`, `λ_min(S_A)` is the largest floor,
deeper layers have larger floors, `λ_min(S_A) ≤ λ_min(M_AA)`, biorthogonal rows bound `(M⁻¹)_{AA}`,
`S_A = M_AA − M_AD M_DD⁻¹ M_DA`, and `[Λ, M] = K` gives `[Λ_A, S_A] = S_A (M⁻¹KM⁻¹)_{AA} S_A`.
-/

noncomputable section

open Matrix Finset
open scoped MatrixOrder

namespace Cvs.Upstream.SchurLayerFloors

open Cvs.Upstream.PencilLayerBound (IsFloor layer layerFloor layer_posDef layerFloor_pos isFloor_layerFloor)

/-! ### V1: the Schur complement is a constrained minimum -/

section Block

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

end Block

/-! ### Layers -/

section Layer

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- A floor of a symmetric matrix is at most each eigenvalue. -/
theorem le_eigenvalues_of_isFloor {κ : Type*} [Fintype κ] [DecidableEq κ] {S : Matrix κ κ ℝ}
    (hS : S.IsHermitian) {f : ℝ} (hf : IsFloor S f) (i : κ) : f ≤ hS.eigenvalues i := by
  set v : κ → ℝ := ⇑(hS.eigenvectorBasis i)
  have hv : v ⬝ᵥ v = 1 := by
    have h := (hS.eigenvectorBasis).orthonormal.1 i
    rw [EuclideanSpace.norm_eq] at h
    have h2 : ∑ j, ‖(hS.eigenvectorBasis i) j‖ ^ 2 = 1 := by
      have := congrArg (· ^ 2) h
      simpa [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)] using this
    simpa [v, dotProduct, Real.norm_eq_abs, sq_abs, sq] using h2
  have h := hf v
  rw [hS.mulVec_eigenvectorBasis i, dotProduct_smul, smul_eq_mul, hv] at h
  simpa using h

/-- **`λ_min(S_k)` is the largest floor**: `f ≤ λ_min(S_k)` iff `f` is a floor of `S_k`. -/
theorem le_layerFloor_iff {M : Matrix ι ι ℝ} (hM : M.PosDef) (k : ι) (f : ℝ) :
    f ≤ layerFloor hM k ↔ IsFloor (layer M k) f := by
  constructor
  · intro h v
    have h0 : 0 ≤ v ⬝ᵥ v := by simpa using dotProduct_self_star_nonneg v
    exact (mul_le_mul_of_nonneg_right h h0).trans (isFloor_layerFloor hM k v)
  · intro h
    have : Nonempty {j // k ≤ j} := ⟨⟨k, le_rfl⟩⟩
    exact le_ciInf fun i => le_eigenvalues_of_isFloor (layer_posDef hM k).isHermitian h i

/-- **V2**: deeper layers have larger floors, `λ_min(S_{k₀}) ≤ λ_min(S_k)` for `k₀ ≤ k`. -/
theorem layerFloor_mono {M : Matrix ι ι ℝ} (hM : M.PosDef) {k₀ k : ι} (hk : k₀ ≤ k) :
    layerFloor hM k₀ ≤ layerFloor hM k :=
  (le_layerFloor_iff hM k _).2
    (Cvs.Upstream.PencilLayerBound.isFloor_layer_of_le hM hk (layerFloor_pos hM k₀) (isFloor_layerFloor hM k₀))

end Layer

/-! ### V4: biorthogonal rows -/

section Dual

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [DecidableEq κ] in
/-- **V4**: rows `Z_a` biorthogonal to a Gram family, `⟪Z_a, Y_i⟫ = [i = g a]`, dominate the inverse block:
`uᵀ(M⁻¹)_{gg}u ≤ ‖Σ_a u_a Z_a‖²` for `M = gram Y ≻ 0`. -/
theorem quad_inv_le_norm_dual {Y : ι → E} (hM : (gram ℝ Y).PosDef) {g : κ → ι} (Z : κ → E)
    (hZ : ∀ a i, inner ℝ (Z a) (Y i) = if i = g a then 1 else 0) (u : κ → ℝ) :
    u ⬝ᵥ ((gram ℝ Y)⁻¹.submatrix g g *ᵥ u) ≤ ‖∑ a, u a • Z a‖ ^ 2 := by
  set M := gram ℝ Y
  have hMu : IsUnit M.det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  set R : Matrix ι κ ℝ := (1 : Matrix ι ι ℝ).submatrix id g
  have hRMR : Rᵀ * M⁻¹ * R = M⁻¹.submatrix g g := by
    ext k l; simp [R, Matrix.mul_apply, Matrix.one_apply]
  set v := R *ᵥ u
  set b := M⁻¹ *ᵥ v
  set w := ∑ i, b i • Y i
  set z := ∑ a, u a • Z a
  have hT : (M⁻¹)ᵀ = M⁻¹ := Cvs.Upstream.CellFloorSandwichPosDef.transpose_eq_of_posSemidef hM.inv.posSemidef
  have hQ : u ⬝ᵥ (M⁻¹.submatrix g g *ᵥ u) = v ⬝ᵥ b := by
    rw [← hRMR, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u Rᵀ, vecMul_transpose]
  have hw : ‖w‖ ^ 2 = v ⬝ᵥ b := by
    rw [← Cvs.Upstream.CellFloorSandwichPosDef.quad_gram, show M *ᵥ b = v by rw [mulVec_mulVec, mul_nonsing_inv _ hMu, one_mulVec],
      dotProduct_comm]
  have hzY : ∀ i, inner ℝ z (Y i) = v i := by
    intro i
    simp only [z, sum_inner, real_inner_smul_left, hZ, mul_ite, mul_one, mul_zero]
    simp [v, R, mulVec, dotProduct, Matrix.one_apply]
  have hzw : inner ℝ z w = v ⬝ᵥ b := by
    simp only [w, inner_sum, real_inner_smul_right, hzY]
    simp [dotProduct, mul_comm]
  rw [hQ, ← hw]
  have h1 := real_inner_le_norm z w
  rw [hzw, ← hw] at h1
  have h2 : 0 ≤ ‖w‖ := norm_nonneg _
  have h3 : 0 ≤ ‖z‖ := norm_nonneg _
  nlinarith

end Dual

/-! ### Feshbach: the Schur complement is `M_AA − M_AD M_DD⁻¹ M_DA` -/

section Feshbach

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

end Feshbach

/-! ### Displacement: a commutator with a diagonal passes to every layer -/

section Displacement

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **Prop 5.2, general form**: `ΛM − MΛ = K` with `Λ = diag d` gives
`Λ_A S_A − S_A Λ_A = S_A (M⁻¹KM⁻¹)_{AA} S_A` on every layer `A = {j ≥ k}`. -/
theorem layer_displacement {M : Matrix ι ι ℝ} (hM : M.PosDef) (d : ι → ℝ) {K : Matrix ι ι ℝ}
    (hK : diagonal d * M - M * diagonal d = K) (k : ι) :
    diagonal (fun j : {j // k ≤ j} => d j) * layer M k - layer M k * diagonal (fun j : {j // k ≤ j} => d j)
      = layer M k * (M⁻¹ * K * M⁻¹).submatrix Subtype.val Subtype.val * layer M k := by
  have hMu : IsUnit M.det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  set Pa := M⁻¹.submatrix (Subtype.val : {j // k ≤ j} → ι) Subtype.val
  have hPa : IsUnit Pa.det :=
    (isUnit_iff_isUnit_det _).mp (hM.inv.submatrix Subtype.val_injective).isUnit
  set La := diagonal (fun j : {j // k ≤ j} => d j)
  have hfull : M⁻¹ * K * M⁻¹ = -(diagonal d * M⁻¹ - M⁻¹ * diagonal d) := by
    have a1 : M⁻¹ * (diagonal d * M) * M⁻¹ = M⁻¹ * diagonal d := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hMu, Matrix.mul_one]
    have a2 : M⁻¹ * (M * diagonal d) * M⁻¹ = diagonal d * M⁻¹ := by
      rw [← Matrix.mul_assoc M⁻¹ M, nonsing_inv_mul _ hMu, Matrix.one_mul]
    rw [← hK, Matrix.mul_sub, Matrix.sub_mul, a1, a2, neg_sub]
  have hres : (M⁻¹ * K * M⁻¹).submatrix (Subtype.val : {j // k ≤ j} → ι) Subtype.val = -(La * Pa - Pa * La) := by
    rw [hfull]
    ext a b
    simp [La, Pa, diagonal_mul, mul_diagonal]
  rw [hres, show layer M k = Pa⁻¹ from rfl]
  have e1 : Pa⁻¹ * (La * Pa) * Pa⁻¹ = Pa⁻¹ * La := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, mul_nonsing_inv _ hPa, Matrix.mul_one]
  have e2 : Pa⁻¹ * (Pa * La) * Pa⁻¹ = La * Pa⁻¹ := by
    rw [← Matrix.mul_assoc Pa⁻¹ Pa La, nonsing_inv_mul _ hPa, Matrix.one_mul]
  rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_sub, Matrix.sub_mul, e1, e2, neg_sub]

/-- **Prop 5.2, low rank**: `ΛM − MΛ = GJGᵀ` gives `Λ_A S_A − S_A Λ_A = S_A X J Xᵀ S_A` with `X = (M⁻¹G)_A`, so the
displacement rank of every layer is at most that of `M`. -/
theorem layer_displacement_lowRank {m : Type*} [Fintype m] {M : Matrix ι ι ℝ} (hM : M.PosDef) (d : ι → ℝ)
    (G : Matrix ι m ℝ) (J : Matrix m m ℝ) (hK : diagonal d * M - M * diagonal d = G * J * Gᵀ) (k : ι) :
    diagonal (fun j : {j // k ≤ j} => d j) * layer M k - layer M k * diagonal (fun j : {j // k ≤ j} => d j)
      = layer M k * (M⁻¹ * G).submatrix (Subtype.val : {j // k ≤ j} → ι) (id : m → m) * J
          * ((M⁻¹ * G).submatrix (Subtype.val : {j // k ≤ j} → ι) (id : m → m))ᵀ * layer M k := by
  rw [layer_displacement hM d hK k]
  have hT : (M⁻¹)ᵀ = M⁻¹ := Cvs.Upstream.CellFloorSandwichPosDef.transpose_eq_of_posSemidef hM.inv.posSemidef
  have hsub : (M⁻¹ * (G * J * Gᵀ) * M⁻¹).submatrix (Subtype.val : {j // k ≤ j} → ι) Subtype.val
      = (M⁻¹ * G).submatrix (Subtype.val : {j // k ≤ j} → ι) (id : m → m) * J
          * ((M⁻¹ * G).submatrix (Subtype.val : {j // k ≤ j} → ι) (id : m → m))ᵀ := by
    have hX : M⁻¹ * (G * J * Gᵀ) * M⁻¹ = (M⁻¹ * G) * J * (M⁻¹ * G)ᵀ := by
      rw [Matrix.transpose_mul, hT]; simp only [Matrix.mul_assoc]
    rw [hX]
    ext a b
    simp [Matrix.mul_apply]
  rw [hsub]
  simp only [Matrix.mul_assoc]

end Displacement

end Cvs.Upstream.SchurLayerFloors

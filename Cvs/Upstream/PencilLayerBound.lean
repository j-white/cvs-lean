import Mathlib
import Cvs.Upstream.CellFloorSandwichPosDef

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The layer bound for the pencil `λ_max(diag μ, M)` on a finite linear order

For `M ≻ 0` let `S_k = ((M⁻¹)_{AA})⁻¹` be the Schur complement onto `A = {j ≥ k}` and `F_k` a floor of `S_k`.
I1: a pencil top over a subset of vectors is at most the full one. I2: `μ_t (M⁻¹)_tt ≤ λ_max`.
Layer bound: if `μ_j = Σ_{k ≤ j} δ_k` with `δ ≥ 0`, then `λ_max(diag μ, M) ≤ Σ_k δ_k/F_k`, and floors pass
to deeper layers, so `λ_max ≤ μ_t/F_{k₀} + Σ_{k < k₀} δ_k/F_k`; `F_k = λ_min(S_k)` is admissible.
-/

noncomputable section

open Matrix Finset
open scoped MatrixOrder

namespace Cvs.Upstream.PencilLayerBound

/-! ### Floors and their inverse form -/

section Floor

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- `f` is a floor of `S`: `f |v|² ≤ vᵀSv` for every `v`. -/
def IsFloor (S : Matrix κ κ ℝ) (f : ℝ) : Prop := ∀ v : κ → ℝ, f * (v ⬝ᵥ v) ≤ v ⬝ᵥ (S *ᵥ v)

/-- A floor `f > 0` of `S ≻ 0` bounds the inverse: `uᵀS⁻¹u ≤ |u|²/f`. -/
theorem quad_inv_le_of_isFloor {S : Matrix κ κ ℝ} (hS : S.PosDef) {f : ℝ} (hf : 0 < f)
    (hF : IsFloor S f) (u : κ → ℝ) : u ⬝ᵥ (S⁻¹ *ᵥ u) ≤ (u ⬝ᵥ u) / f := by
  have hu : IsUnit S.det := (isUnit_iff_isUnit_det _).mp hS.isUnit
  set w := S⁻¹ *ᵥ u
  have hSw : S *ᵥ w = u := by rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have h := hF w
  rw [hSw] at h
  have hsq : 0 ≤ (f • w - u) ⬝ᵥ (f • w - u) := by
    simpa using dotProduct_self_star_nonneg (f • w - u)
  have hexp : (f • w - u) ⬝ᵥ (f • w - u) = f ^ 2 * (w ⬝ᵥ w) - 2 * f * (w ⬝ᵥ u) + u ⬝ᵥ u := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm u w]
    ring
  rw [dotProduct_comm u w, le_div_iff₀ hf]
  nlinarith

/-- An upper bound `uᵀSu ≤ c|u|²` with `c > 0` and `S ≻ 0` gives the floor `1/c` of `S⁻¹`. -/
theorem isFloor_inv_of_quad_le {S : Matrix κ κ ℝ} (hS : S.PosDef) {c : ℝ} (hc : 0 < c)
    (hU : ∀ u : κ → ℝ, u ⬝ᵥ (S *ᵥ u) ≤ c * (u ⬝ᵥ u)) : IsFloor S⁻¹ (1 / c) := by
  intro v
  have hu : IsUnit S.det := (isUnit_iff_isUnit_det _).mp hS.isUnit
  have h := Cvs.Upstream.CellFloorSandwichPosDef.two_mul_dot_sub_inv_le hS.inv (c⁻¹ • v) v
  rw [nonsing_inv_nonsing_inv _ hu] at h
  have h2 : (S *ᵥ (c⁻¹ • v)) ⬝ᵥ (c⁻¹ • v) = c⁻¹ ^ 2 * (v ⬝ᵥ (S *ᵥ v)) := by
    rw [dotProduct_comm]; simp [mulVec_smul, smul_dotProduct, dotProduct_smul]; ring
  have h1 : (c⁻¹ • v) ⬝ᵥ v = c⁻¹ * (v ⬝ᵥ v) := by simp
  rw [h1, h2] at h
  have hv := hU v
  have hci : 0 < c⁻¹ := inv_pos.mpr hc
  have : c⁻¹ ^ 2 * (v ⬝ᵥ (S *ᵥ v)) ≤ c⁻¹ * (v ⬝ᵥ v) := by
    calc c⁻¹ ^ 2 * (v ⬝ᵥ (S *ᵥ v)) ≤ c⁻¹ ^ 2 * (c * (v ⬝ᵥ v)) :=
          mul_le_mul_of_nonneg_left hv (by positivity)
      _ = c⁻¹ * (v ⬝ᵥ v) := by field_simp
  rw [one_div]
  linarith

/-- An upper bound on a quadratic form passes to a principal submatrix along an injective `g`. -/
theorem quad_submatrix_le {α : Type*} [Fintype α] [DecidableEq α] {Q : Matrix α α ℝ} {c : ℝ}
    (hU : ∀ w : α → ℝ, w ⬝ᵥ (Q *ᵥ w) ≤ c * (w ⬝ᵥ w)) {g : κ → α} (hg : Function.Injective g)
    (u : κ → ℝ) : u ⬝ᵥ (Q.submatrix g g *ᵥ u) ≤ c * (u ⬝ᵥ u) := by
  set R : Matrix α κ ℝ := (1 : Matrix α α ℝ).submatrix id g
  have hRQR : Rᵀ * Q * R = Q.submatrix g g := by
    ext k l; simp [R, Matrix.mul_apply, Matrix.one_apply]
  have hRR : Rᵀ * R = 1 := by
    ext k l; simp [R, Matrix.mul_apply, Matrix.one_apply, hg.eq_iff]
  have key : ∀ P : Matrix α α ℝ, u ⬝ᵥ ((Rᵀ * P * R) *ᵥ u) = (R *ᵥ u) ⬝ᵥ (P *ᵥ (R *ᵥ u)) := by
    intro P
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u Rᵀ, vecMul_transpose]
  have h1 := key Q
  have h2 := key 1
  rw [hRQR] at h1
  rw [Matrix.mul_one, hRR, one_mulVec, one_mulVec] at h2
  rw [h1, h2]
  exact hU _

/-- A Hermitian matrix whose eigenvalues are all at least `f` has floor `f`. -/
theorem isFloor_of_eigenvalues {S : Matrix κ κ ℝ} (hS : S.IsHermitian) {f : ℝ}
    (hf : ∀ i, f ≤ hS.eigenvalues i) : IsFloor S f := by
  have hle : f • (1 : Matrix κ κ ℝ) ≤ S := by
    have h1 : f • (1 : Matrix κ κ ℝ) = algebraMap ℝ (Matrix κ κ ℝ) f := by
      rw [Algebra.algebraMap_eq_smul_one]
    rw [h1, algebraMap_le_iff_le_spectrum (hS.isSelfAdjoint), hS.spectrum_real_eq_range_eigenvalues]
    rintro _ ⟨i, rfl⟩
    exact hf i
  intro v
  have h := (Matrix.le_iff.mp hle).dotProduct_mulVec_nonneg v
  simp only [star_trivial, sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul] at h
  linarith

end Floor

/-! ### The pencil top and I1, I2 -/

section Pencil

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The pencil top on a set `T` of vectors: the least `c ≥ 0` with `Σ_j μ_j b_j² ≤ c bᵀMb` on `T`. -/
def pencilTop (μ : ι → ℝ) (M : Matrix ι ι ℝ) (T : Set (ι → ℝ)) : ℝ :=
  sInf {c | 0 ≤ c ∧ ∀ b ∈ T, ∑ j, μ j * b j ^ 2 ≤ c * b ⬝ᵥ (M *ᵥ b)}

/-- The admissible constants of a positive definite pencil with `μ ≥ 0` form a nonempty set. -/
theorem pencilTop_nonempty {M : Matrix ι ι ℝ} (hM : M.PosDef) {μ : ι → ℝ} (hμ : ∀ j, 0 ≤ μ j)
    (T : Set (ι → ℝ)) :
    {c | 0 ≤ c ∧ ∀ b ∈ T, ∑ j, μ j * b j ^ 2 ≤ c * b ⬝ᵥ (M *ᵥ b)}.Nonempty :=
  ⟨∑ j, μ j / Cvs.Upstream.CellFloorSandwichPosDef.sigmaP M j,
    Finset.sum_nonneg fun j _ => div_nonneg (hμ j) (Cvs.Upstream.CellFloorSandwichPosDef.sigmaP_pos hM j).le,
    fun b _ => Cvs.Upstream.CellFloorSandwichPosDef.sum_weight_le hM hμ b⟩

omit [DecidableEq ι] in
/-- Every admissible constant bounds the pencil top. -/
theorem pencilTop_le {μ : ι → ℝ} {M : Matrix ι ι ℝ} {T : Set (ι → ℝ)} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ b ∈ T, ∑ j, μ j * b j ^ 2 ≤ c * b ⬝ᵥ (M *ᵥ b)) : pencilTop μ M T ≤ c :=
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨hc, h⟩

/-- The pencil top is nonnegative. -/
theorem pencilTop_nonneg {M : Matrix ι ι ℝ} (hM : M.PosDef) {μ : ι → ℝ} (hμ : ∀ j, 0 ≤ μ j)
    (T : Set (ι → ℝ)) : 0 ≤ pencilTop μ M T :=
  le_csInf (pencilTop_nonempty hM hμ T) fun _ hx => hx.1

/-- The pencil top is admissible: `Σ_j μ_j b_j² ≤ pencilTop · bᵀMb` on `T`. -/
theorem sum_le_pencilTop {M : Matrix ι ι ℝ} (hM : M.PosDef) {μ : ι → ℝ} (hμ : ∀ j, 0 ≤ μ j)
    {T : Set (ι → ℝ)} {b : ι → ℝ} (hb : b ∈ T) :
    ∑ j, μ j * b j ^ 2 ≤ pencilTop μ M T * b ⬝ᵥ (M *ᵥ b) := by
  have hq : 0 ≤ b ⬝ᵥ (M *ᵥ b) := by simpa using hM.posSemidef.dotProduct_mulVec_nonneg b
  rcases hq.eq_or_lt with hq0 | hqp
  · obtain ⟨c, _, hc⟩ := pencilTop_nonempty hM hμ T
    have := hc b hb
    rw [← hq0, mul_zero] at this ⊢
    exact this
  · rw [← div_le_iff₀ hqp]
    refine le_csInf (pencilTop_nonempty hM hμ T) fun c hc => ?_
    rw [div_le_iff₀ hqp]
    exact hc.2 b hb

end Pencil

/-! ### Layers of a finite linear order -/

section Layer

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The Schur complement of `M` onto the layer `{j : k ≤ j}`, written `((M⁻¹)_{AA})⁻¹`. -/
def layer (M : Matrix ι ι ℝ) (k : ι) : Matrix {j // k ≤ j} {j // k ≤ j} ℝ :=
  (M⁻¹.submatrix Subtype.val Subtype.val)⁻¹

/-- The Schur complement onto a layer is positive definite. -/
theorem layer_posDef {M : Matrix ι ι ℝ} (hM : M.PosDef) (k : ι) : (layer M k).PosDef :=
  (hM.inv.submatrix Subtype.val_injective).inv

/-- The floor `λ_min(S_k)` of the Schur complement onto the layer `{j ≥ k}`. -/
def layerFloor {M : Matrix ι ι ℝ} (hM : M.PosDef) (k : ι) : ℝ :=
  ⨅ i, (layer_posDef hM k).isHermitian.eigenvalues i

/-- `λ_min(S_k)` is a floor of `S_k`. -/
theorem isFloor_layerFloor {M : Matrix ι ι ℝ} (hM : M.PosDef) (k : ι) :
    IsFloor (layer M k) (layerFloor hM k) :=
  isFloor_of_eigenvalues _ fun i => ciInf_le (Set.finite_range _).bddBelow i

/-- `λ_min(S_k)` is positive. -/
theorem layerFloor_pos {M : Matrix ι ι ℝ} (hM : M.PosDef) (k : ι) : 0 < layerFloor hM k := by
  have : Nonempty {j // k ≤ j} := ⟨⟨k, le_rfl⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := (layer_posDef hM k).isHermitian.eigenvalues)
  rw [layerFloor, ← hi]
  exact (layer_posDef hM k).eigenvalues_pos i

/-- The layer sum of squares is the self dot product of the restriction. -/
theorem dot_restrict (b : ι → ℝ) (k : ι) :
    (fun j : {j // k ≤ j} => b j.1) ⬝ᵥ (fun j => b j.1) = ∑ j ∈ univ.filter (k ≤ ·), b j ^ 2 := by
  simp only [dotProduct, ← sq]
  exact (Finset.sum_subtype _ (by simp) (fun j => b j ^ 2)).symm

/-- A layer floor bounds the layer mass: `F_k Σ_{j ≥ k} b_j² ≤ bᵀMb`. -/
theorem mul_sum_layer_le {M : Matrix ι ι ℝ} (hM : M.PosDef) {k : ι} {f : ℝ}
    (hF : IsFloor (layer M k) f) (b : ι → ℝ) :
    f * ∑ j ∈ univ.filter (k ≤ ·), b j ^ 2 ≤ b ⬝ᵥ (M *ᵥ b) := by
  rw [← dot_restrict]
  exact (hF _).trans (Cvs.Upstream.CellFloorSandwichPosDef.block_quad_le hM Subtype.val_injective b)

/-- A floor of a layer is a floor of every deeper layer. -/
theorem isFloor_layer_of_le {M : Matrix ι ι ℝ} (hM : M.PosDef) {k₀ k : ι} (hk : k₀ ≤ k) {f : ℝ}
    (hf : 0 < f) (hF : IsFloor (layer M k₀) f) : IsFloor (layer M k) f := by
  set P := M⁻¹.submatrix (Subtype.val : {j // k₀ ≤ j} → ι) Subtype.val
  have hP : P.PosDef := hM.inv.submatrix Subtype.val_injective
  have hPu : IsUnit P.det := (isUnit_iff_isUnit_det _).mp hP.isUnit
  have hU : ∀ u, u ⬝ᵥ (P *ᵥ u) ≤ f⁻¹ * (u ⬝ᵥ u) := by
    intro u
    have h := quad_inv_le_of_isFloor (layer_posDef hM k₀) hf hF u
    rw [layer, nonsing_inv_nonsing_inv _ hPu] at h
    rwa [div_eq_inv_mul] at h
  set g : {j // k ≤ j} → {j // k₀ ≤ j} := fun j => ⟨j.1, hk.trans j.2⟩
  have hg : Function.Injective g := fun a b h => Subtype.ext (by simpa [g] using congrArg Subtype.val h)
  have hB : P.submatrix g g = M⁻¹.submatrix Subtype.val Subtype.val := rfl
  have h := isFloor_inv_of_quad_le (hP.submatrix hg) (inv_pos.mpr hf) (quad_submatrix_le hU hg)
  rw [hB, one_div, inv_inv] at h
  exact h

/-- **Layer bound**: `μ_j = Σ_{k ≤ j} δ_k`, `δ ≥ 0` and floors `F_k > 0` give
`Σ_j μ_j b_j² ≤ (Σ_k δ_k/F_k) bᵀMb`. -/
theorem sum_le_layer {M : Matrix ι ι ℝ} (hM : M.PosDef) {μ δ F : ι → ℝ} (hδ : ∀ k, 0 ≤ δ k)
    (hμ : ∀ j, μ j = ∑ k ∈ univ.filter (· ≤ j), δ k) (hF0 : ∀ k, 0 < F k)
    (hF : ∀ k, IsFloor (layer M k) (F k)) (b : ι → ℝ) :
    ∑ j, μ j * b j ^ 2 ≤ (∑ k, δ k / F k) * b ⬝ᵥ (M *ᵥ b) := by
  have hswap : ∑ j, μ j * b j ^ 2 = ∑ k, δ k * ∑ j ∈ univ.filter (k ≤ ·), b j ^ 2 := by
    simp only [hμ, Finset.sum_mul, Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  rw [hswap, Finset.sum_mul]
  refine Finset.sum_le_sum fun k _ => ?_
  have h := mul_sum_layer_le hM (hF k) b
  rw [div_mul_eq_mul_div, le_div_iff₀ (hF0 k), mul_assoc, mul_comm _ (F k)]
  exact mul_le_mul_of_nonneg_left h (hδ k)

/-- **Theorem A**: `λ_max(diag μ, M) ≤ Σ_k δ_k/λ_min(S_k)` for `μ_j = Σ_{k ≤ j} δ_k` with `δ ≥ 0`. -/
theorem pencilTop_le_layer {M : Matrix ι ι ℝ} (hM : M.PosDef) {μ δ : ι → ℝ} (hδ : ∀ k, 0 ≤ δ k)
    (hμ : ∀ j, μ j = ∑ k ∈ univ.filter (· ≤ j), δ k) :
    pencilTop μ M Set.univ ≤ ∑ k, δ k / layerFloor hM k :=
  pencilTop_le (Finset.sum_nonneg fun k _ => div_nonneg (hδ k) (layerFloor_pos hM k).le)
    fun b _ => sum_le_layer hM hδ hμ (layerFloor_pos hM) (isFloor_layerFloor hM) b

end Layer

end Cvs.Upstream.PencilLayerBound

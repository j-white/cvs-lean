import Mathlib
import Cvs.Upstream.PencilLayerBound
import Cvs.Upstream.TwistedPairLayerFloor

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The full-twist floor of a layer

For `0 ≺ M ≼ 1` the layer floor `F = λ_min(S_A)`, `A = {j ≥ k}`, is attained at a vector `v` with `|v_A| = 1` whose
image `Mv` equals `F·v` on `A` and vanishes off `A`. Twisting every coordinate, `D = diag(d)` with `d₀ ≤ d ≤ 1` on `A`,
a floor `1 − ε` of `M + DMD` on `A` gives `F ≥ ½ − (ε + ρ)/(2d₀)`, where `ρ` bounds the far twist
`Σ_{j<k} (1 − d_j)²v_j²` on the vectors whose image vanishes off `A`.
-/

noncomputable section

open Matrix Finset

namespace Cvs.Upstream.FullTwistLayerFloor

open Cvs.Upstream.PencilLayerBound (layer layerFloor layer_posDef)
open Cvs.Upstream.TwistedPairLayerFloor (emb emb_mulVec emb_transpose_mulVec)

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The full twist `Dv`: multiply every coordinate `v_j` by `d_j`. -/
def twistAll (d v : ι → ℝ) : ι → ℝ := fun j => d j * v j

/-- **The layer minimiser**: some `v` has `Σ_{j ≥ k} v_j² = 1` and `(Mv)_j = F_k v_j` on `{j ≥ k}`, `0` off it. -/
theorem exists_layer_minimiser {M : Matrix ι ι ℝ} (hM : M.PosDef) (k : ι) :
    ∃ v : ι → ℝ, ∑ j ∈ univ.filter (k ≤ ·), v j ^ 2 = 1 ∧
      ∀ j, (M *ᵥ v) j = if k ≤ j then layerFloor hM k * v j else 0 := by
  set S := layer M k
  have hS := (layer_posDef hM k).isHermitian
  have : Nonempty {j // k ≤ j} := ⟨⟨k, le_rfl⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := hS.eigenvalues)
  set F := layerFloor hM k
  have hFi : hS.eigenvalues i = F := hi
  set e : {j // k ≤ j} → ℝ := ⇑(hS.eigenvectorBasis i)
  have he : e ⬝ᵥ e = 1 := by
    have h := (hS.eigenvectorBasis).orthonormal.1 i
    rw [EuclideanSpace.norm_eq] at h
    have h2 : ∑ j, ‖(hS.eigenvectorBasis i) j‖ ^ 2 = 1 := by
      have := congrArg (· ^ 2) h
      simpa [Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)] using this
    simpa [e, dotProduct, Real.norm_eq_abs, sq_abs, sq] using h2
  have hSe : S *ᵥ e = F • e := by rw [← hFi]; exact hS.mulVec_eigenvectorBasis i
  set R := emb k
  set P := M⁻¹.submatrix (Subtype.val : {j // k ≤ j} → ι) Subtype.val
  have hPu : IsUnit P.det := (isUnit_iff_isUnit_det _).mp (hM.inv.submatrix Subtype.val_injective).isUnit
  have hMu : IsUnit M.det := (isUnit_iff_isUnit_det _).mp hM.isUnit
  have hRMR : Rᵀ * M⁻¹ * R = P := by ext a b; simp [R, emb, P, Matrix.mul_apply, Matrix.one_apply]
  set v : ι → ℝ := M⁻¹ *ᵥ (R *ᵥ (F • e))
  have hvA : Rᵀ *ᵥ v = e := by
    have : P *ᵥ (S *ᵥ e) = e := by
      rw [mulVec_mulVec, show S = P⁻¹ from rfl, mul_nonsing_inv _ hPu, one_mulVec]
    rw [hSe] at this
    simp only [v, mulVec_mulVec, ← Matrix.mul_assoc, hRMR]; exact this
  have hMv : M *ᵥ v = F • (R *ᵥ e) := by
    simp only [v]; rw [mulVec_mulVec, mul_nonsing_inv _ hMu, one_mulVec, mulVec_smul]
  have hvj : ∀ j (h : k ≤ j), v j = e ⟨j, h⟩ := fun j h => by
    have := congrFun hvA ⟨j, h⟩
    rwa [emb_transpose_mulVec] at this
  refine ⟨v, ?_, fun j => ?_⟩
  · rw [← Cvs.Upstream.PencilLayerBound.dot_restrict, ← he]
    congr 1 <;> ext a <;> rw [← hvA, emb_transpose_mulVec]
  · rw [hMv, Pi.smul_apply, emb_mulVec, smul_eq_mul]
    split_ifs with h
    · rw [hvj j h]
    · simp

/-- **The full-twist floor**: for `0 ≺ M ≼ 1`, `d₀ ≤ d ≤ 1` on `{j ≥ k}`, the far-twist bound `ρ` on the vectors
whose image vanishes off `{j ≥ k}`, `0 ≤ ε + ρ`, and `(1 − ε)Σ_{j ≥ k} v_j² ≤ vᵀMv + (Dv)ᵀM(Dv)` for every `v`,
the layer floor is at least `½ − (ε + ρ)/(2d₀)`. -/
theorem half_sub_le_layerFloor_full {M : Matrix ι ι ℝ} (hM : M.PosDef)
    (hle : ∀ w : ι → ℝ, w ⬝ᵥ (M *ᵥ w) ≤ w ⬝ᵥ w) {k : ι} {d : ι → ℝ} {d₀ ε ρ : ℝ} (hd₀ : 0 < d₀)
    (hd : ∀ j, k ≤ j → d₀ ≤ d j ∧ d j ≤ 1) (hερ : 0 ≤ ε + ρ)
    (hρ : ∀ v : ι → ℝ, (∀ j, ¬ k ≤ j → (M *ᵥ v) j = 0) →
      ∑ j ∈ univ.filter (fun j => ¬ k ≤ j), (1 - d j) ^ 2 * v j ^ 2 ≤ ρ * ∑ j ∈ univ.filter (k ≤ ·), v j ^ 2)
    (hN : ∀ v : ι → ℝ, (1 - ε) * ∑ j ∈ univ.filter (k ≤ ·), v j ^ 2
      ≤ v ⬝ᵥ (M *ᵥ v) + twistAll d v ⬝ᵥ (M *ᵥ twistAll d v)) :
    1 / 2 - (ε + ρ) / (2 * d₀) ≤ layerFloor hM k := by
  obtain ⟨v, hmass, hMv⟩ := exists_layer_minimiser hM k
  set F := layerFloor hM k
  have hF : 0 < F := Cvs.Upstream.PencilLayerBound.layerFloor_pos hM k
  have hT : Mᵀ = M := by
    have := hM.isHermitian; rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hsymm : ∀ a b : ι → ℝ, a ⬝ᵥ (M *ᵥ b) = b ⬝ᵥ (M *ᵥ a) := fun a b => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]
  -- the pairing of any `w` with `Mv`
  have hpair : ∀ w : ι → ℝ, w ⬝ᵥ (M *ᵥ v) = F * ∑ j ∈ univ.filter (k ≤ ·), w j * v j := fun w => by
    simp only [dotProduct, hMv, Finset.mul_sum, Finset.sum_filter]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
  set w : ι → ℝ := fun j => (d j - 1) * v j
  have htw : twistAll d v = v + w := by ext j; simp only [twistAll, w, Pi.add_apply]; ring
  set s := ∑ j ∈ univ.filter (k ≤ ·), d j * v j ^ 2
  have hq : v ⬝ᵥ (M *ᵥ v) = F := by
    rw [hpair]; simp only [← sq]; rw [hmass, mul_one]
  have hcross : w ⬝ᵥ (M *ᵥ v) = F * (s - 1) := by
    rw [hpair, ← hmass, ← Finset.sum_sub_distrib]
    congr 1; exact Finset.sum_congr rfl fun j _ => by simp only [w]; ring
  have hfar : ∑ j ∈ univ.filter (fun j => ¬ k ≤ j), (1 - d j) ^ 2 * v j ^ 2 ≤ ρ := by
    have := hρ v fun j hj => by rw [hMv, ite_eq_right hj]
    rwa [hmass, mul_one] at this
  have hww : w ⬝ᵥ (M *ᵥ w) ≤ 1 - s + ρ := by
    refine (hle w).trans ?_
    have hsplit : w ⬝ᵥ w = ∑ j ∈ univ.filter (k ≤ ·), (1 - d j) ^ 2 * v j ^ 2
        + ∑ j ∈ univ.filter (fun j => ¬ k ≤ j), (1 - d j) ^ 2 * v j ^ 2 := by
      rw [Finset.sum_filter_add_sum_filter_not]
      simp only [dotProduct, w]; exact Finset.sum_congr rfl fun j _ => by ring
    have hA : ∑ j ∈ univ.filter (k ≤ ·), (1 - d j) ^ 2 * v j ^ 2 ≤ 1 - s := by
      have e : 1 - s = ∑ j ∈ univ.filter (k ≤ ·), (v j ^ 2 - d j * v j ^ 2) := by
        rw [Finset.sum_sub_distrib, hmass]
      rw [e]
      refine Finset.sum_le_sum fun j hj => ?_
      obtain ⟨h0, h1⟩ := hd j (Finset.mem_filter.1 hj).2
      have hd0 : 0 ≤ d j := hd₀.le.trans h0
      nlinarith [sq_nonneg (v j), mul_nonneg (mul_nonneg hd0 (sub_nonneg.2 h1)) (sq_nonneg (v j))]
    linarith
  have hexp : twistAll d v ⬝ᵥ (M *ᵥ twistAll d v)
      = v ⬝ᵥ (M *ᵥ v) + 2 * (w ⬝ᵥ (M *ᵥ v)) + w ⬝ᵥ (M *ᵥ w) := by
    rw [htw, mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hsymm v w]; ring
  have hs : d₀ ≤ s := by
    calc d₀ = ∑ j ∈ univ.filter (k ≤ ·), d₀ * v j ^ 2 := by rw [← Finset.mul_sum, hmass, mul_one]
      _ ≤ s := Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_right (hd j (Finset.mem_filter.1 hj).2).1 (sq_nonneg _)
  have hmain := hN v
  rw [hmass, hexp, hq, hcross] at hmain
  -- `1 − ε ≤ 2Fs + 1 − s + ρ`, hence `2Fs ≥ s − ε − ρ`
  have key : s - (ε + ρ) ≤ 2 * F * s := by nlinarith
  have hs0 : 0 < s := hd₀.trans_le hs
  have h2 : (s - (ε + ρ)) / (2 * s) ≤ F := by rw [div_le_iff₀ (by positivity)]; linarith
  have h3 : (ε + ρ) / (2 * s) ≤ (ε + ρ) / (2 * d₀) := div_le_div_of_nonneg_left hερ (by positivity) (by linarith)
  have h4 : (s - (ε + ρ)) / (2 * s) = 1 / 2 - (ε + ρ) / (2 * s) := by field_simp
  linarith

end Cvs.Upstream.FullTwistLayerFloor

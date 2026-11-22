import Mathlib
import Cvs.StepA.Edge.DeepJointShare

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Projections bounded by interpolants and dual vectors, and the joint split

Three inner-product facts carry Case ∞ of hV. A vector `v` in a larger space that reproduces the pairings of `f`
with `U` bounds `‖P_U f‖ ≤ ‖v‖`. A vector orthogonal to `U` bounds `|⟪V, v⟫| ≤ ‖v‖·‖V − P_U V‖`. And the
projection of `V` on `A ⊔ B` splits as `r + u` with `u = P_B(V − r)`, so `⟪u, U'⟫ = ⟪V − r, P_B U'⟫`.
-/

noncomputable section

open Real Filter
open scoped InnerProductSpace

namespace Cvs.Upstream.ProjectionInterpolantSplit
open Cvs.ZeroCounting

section Duality

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-- **A projection is bounded by any interpolant**: if `⟪ι u, v⟫ = ⟪u, f⟫` on `U` for an isometry `ι`, then
`‖P_U f‖ ≤ ‖v‖`. -/
theorem norm_starProjection_le_of_inner_eq (ι : E →ₗᵢ[ℝ] F) (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (f : E) (v : F) (h : ∀ u ∈ U, ⟪ι u, v⟫_ℝ = ⟪u, f⟫_ℝ) : ‖U.starProjection f‖ ≤ ‖v‖ := by
  set p := U.starProjection f
  have hp : p ∈ U := U.starProjection_apply_mem f
  have h1 : ‖p‖ ^ 2 = ⟪p, f⟫_ℝ := by
    have h0 : ⟪f - p, p⟫_ℝ = 0 := U.starProjection_inner_eq_zero f p hp
    rw [inner_sub_left] at h0
    have c := real_inner_comm p f
    have e := real_inner_self_eq_norm_sq p
    linarith
  have h2 : ‖p‖ ^ 2 ≤ ‖p‖ * ‖v‖ := by
    rw [h1, ← h p hp]
    calc ⟪ι p, v⟫_ℝ ≤ ‖ι p‖ * ‖v‖ := real_inner_le_norm _ _
      _ = ‖p‖ * ‖v‖ := by rw [ι.norm_map]
  rcases (norm_nonneg p).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg v
  · nlinarith

/-- **Interpolants with a uniform constant bound the projection on `A`**: if every `a ∈ A` has an interpolant
of norm `≤ C‖a‖`, then `‖P_U a‖ ≤ C‖a‖` on `A`. -/
theorem norm_starProjection_le_of_interp (ι : E →ₗᵢ[ℝ] F) (A U : Submodule ℝ E) [U.HasOrthogonalProjection]
    {C : ℝ} (h : ∀ a ∈ A, ∃ v : F, (∀ u ∈ U, ⟪ι u, v⟫_ℝ = ⟪u, a⟫_ℝ) ∧ ‖v‖ ≤ C * ‖a‖) :
    ∀ a ∈ A, ‖U.starProjection a‖ ≤ C * ‖a‖ := fun a ha => by
  obtain ⟨v, hv, hn⟩ := h a ha
  exact (norm_starProjection_le_of_inner_eq ι U a v hv).trans hn

/-- **The angle from interpolants**: under the same hypothesis with `C ≥ 0`, `‖P_U P_A‖ ≤ C`. -/
theorem opNorm_comp_le_of_interp (ι : E →ₗᵢ[ℝ] F) (A U : Submodule ℝ E) [A.HasOrthogonalProjection]
    [U.HasOrthogonalProjection] {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ a ∈ A, ∃ v : F, (∀ u ∈ U, ⟪ι u, v⟫_ℝ = ⟪u, a⟫_ℝ) ∧ ‖v‖ ≤ C * ‖a‖) :
    ‖U.starProjection ∘L A.starProjection‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun f => ?_
  rw [ContinuousLinearMap.comp_apply]
  exact (norm_starProjection_le_of_interp ι A U h _ (A.starProjection_apply_mem f)).trans
    (mul_le_mul_of_nonneg_left (A.norm_starProjection_apply_le f) hC)

/-- **A dual vector bounds the distance from below**: if `v ⊥ ι U`, then `|⟪ι V, v⟫| ≤ ‖V − P_U V‖·‖v‖`. -/
theorem abs_inner_le_dist_mul (ι : E →ₗᵢ[ℝ] F) (U : Submodule ℝ E) [U.HasOrthogonalProjection] (V : E) (v : F)
    (hv : ∀ u ∈ U, ⟪ι u, v⟫_ℝ = 0) : |⟪ι V, v⟫_ℝ| ≤ ‖V - U.starProjection V‖ * ‖v‖ := by
  have e : ⟪ι V, v⟫_ℝ = ⟪ι (V - U.starProjection V), v⟫_ℝ := by
    rw [map_sub, inner_sub_left, hv _ (U.starProjection_apply_mem V), sub_zero]
  rw [e]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [ι.norm_map]

/-- **Squared form of the dual bound**: `⟪ι V, v⟫² ≤ ‖v‖²‖V − P_U V‖²` for `v ⊥ ι U`. -/
theorem sq_inner_le_of_dual (ι : E →ₗᵢ[ℝ] F) (U : Submodule ℝ E) [U.HasOrthogonalProjection] (V : E) (v : F)
    (hv : ∀ u ∈ U, ⟪ι u, v⟫_ℝ = 0) : ⟪ι V, v⟫_ℝ ^ 2 ≤ ‖v‖ ^ 2 * ‖V - U.starProjection V‖ ^ 2 := by
  have h := abs_inner_le_dist_mul ι U V v hv
  have h2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at h2
  nlinarith [h2]

end Duality

section Split

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A B : Submodule ℝ E)
  [B.HasOrthogonalProjection] [(A ⊔ B).HasOrthogonalProjection]

omit [B.HasOrthogonalProjection] in
/-- The projection on `A ⊔ B` splits as `r + u` with `r ∈ A`, `u ∈ B`. -/
theorem exists_split (V : E) : ∃ r ∈ A, ∃ u ∈ B, (A ⊔ B).starProjection V = r + u := by
  obtain ⟨r, hr, u, hu, h⟩ := Submodule.mem_sup.mp ((A ⊔ B).starProjection_apply_mem V)
  exact ⟨r, hr, u, hu, h.symm⟩

/-- **The `B`-part of the split is a projection**: `P_{A⊔B}V = r + u`, `u ∈ B`, gives `u = P_B(V − r)`. -/
theorem starProjection_sub_eq_of_split {V r u : E} (hu : u ∈ B) (h : (A ⊔ B).starProjection V = r + u) :
    B.starProjection (V - r) = u := by
  refine B.eq_starProjection_of_mem_of_inner_eq_zero hu fun b hb => ?_
  have e : V - r - u = V - (A ⊔ B).starProjection V := by rw [h]; abel
  rw [e]
  exact (A ⊔ B).starProjection_inner_eq_zero V b (le_sup_right (a := A) hb)

/-- **The `B`-part pairs through the projection** (Lemma C's reduction): `⟪u, U'⟫ = ⟪V − r, P_B U'⟫`. -/
theorem inner_split_eq {V r u : E} (hu : u ∈ B) (h : (A ⊔ B).starProjection V = r + u) (U' : E) :
    ⟪u, U'⟫_ℝ = ⟪V - r, B.starProjection U'⟫_ℝ := by
  rw [← starProjection_sub_eq_of_split A B hu h, Submodule.inner_starProjection_left_eq_right]

/-- `|⟪u, U'⟫| ≤ ‖V − r‖·‖P_B U'‖` for the `B`-part `u` of the split. -/
theorem abs_inner_split_le {V r u : E} (hu : u ∈ B) (h : (A ⊔ B).starProjection V = r + u) (U' : E) :
    |⟪u, U'⟫_ℝ| ≤ ‖V - r‖ * ‖B.starProjection U'‖ := by
  rw [inner_split_eq A B hu h]
  exact abs_real_inner_le_norm _ _

/-- **The split is coercive at angle `θ < 1`**: with `‖P_B a‖ ≤ θ‖a‖` on `A`,
`(1 − θ)(‖r‖² + ‖u‖²) ≤ ‖V‖²`. -/
theorem split_coercive {V r u : E} (hr : r ∈ A) (hu : u ∈ B) (h : (A ⊔ B).starProjection V = r + u) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ : ∀ a ∈ A, ‖B.starProjection a‖ ≤ θ * ‖a‖) :
    (1 - θ) * (‖r‖ ^ 2 + ‖u‖ ^ 2) ≤ ‖V‖ ^ 2 := by
  have hru : |⟪r, u⟫_ℝ| ≤ θ * ‖r‖ * ‖u‖ := by
    have e : ⟪r, u⟫_ℝ = ⟪B.starProjection r, u⟫_ℝ := by
      rw [Submodule.inner_starProjection_left_eq_right, (B.starProjection_eq_self_iff).2 hu]
    rw [e]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hθ r hr) (norm_nonneg _))
  have hsq : ‖r + u‖ ^ 2 = ‖r‖ ^ 2 + 2 * ⟪r, u⟫_ℝ + ‖u‖ ^ 2 := norm_add_sq_real r u
  have hle : ‖r + u‖ ≤ ‖V‖ := h ▸ (A ⊔ B).norm_starProjection_apply_le V
  have hle2 : ‖r + u‖ ^ 2 ≤ ‖V‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hamgm : 2 * (‖r‖ * ‖u‖) ≤ ‖r‖ ^ 2 + ‖u‖ ^ 2 := by nlinarith [sq_nonneg (‖r‖ - ‖u‖)]
  have h3 := neg_abs_le ⟪r, u⟫_ℝ
  nlinarith [mul_le_mul_of_nonneg_left hamgm hθ0]

/-- **The `A`-part of the split**: `‖r‖ ≤ ‖P_A V‖ + θ‖u‖` when `‖P_B a‖ ≤ θ‖a‖` on `A`, `θ ≥ 0`. -/
theorem norm_split_left_le [A.HasOrthogonalProjection] {V r u : E} (hr : r ∈ A) (hu : u ∈ B)
    (h : (A ⊔ B).starProjection V = r + u) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : ∀ a ∈ A, ‖B.starProjection a‖ ≤ θ * ‖a‖) : ‖r‖ ≤ ‖A.starProjection V‖ + θ * ‖u‖ := by
  have hPA : A.starProjection V = r + A.starProjection u := by
    have e1 : A.starProjection ((A ⊔ B).starProjection V) = A.starProjection V := by
      rw [← ContinuousLinearMap.comp_apply, Submodule.starProjection_comp_starProjection_of_le le_sup_left]
    rw [← e1, h, map_add, (A.starProjection_eq_self_iff).2 hr]
  have hs := Cvs.StepA.Edge.DeepJointShare.norm_starProjection_le_symm A B hθ0 hθ u hu
  have e2 : r = A.starProjection V - A.starProjection u := by rw [hPA]; abel
  rw [e2]
  exact (norm_sub_le _ _).trans (by linarith)

end Split

section Sums

/-- **The three-term weighted split**: for `m ≥ 0` with `m a²`, `m b²`, `m c²` summable, `m (a − b − c)²` is
summable and `Σ m (a − b − c)² ≤ 3(Σ m a² + Σ m b² + Σ m c²)`. -/
theorem tsum_mul_sub_sub_sq_le {ι : Type*} {m a b c : ι → ℝ} (hm : ∀ i, 0 ≤ m i)
    (ha : Summable fun i => m i * a i ^ 2) (hb : Summable fun i => m i * b i ^ 2)
    (hc : Summable fun i => m i * c i ^ 2) :
    (Summable fun i => m i * (a i - b i - c i) ^ 2)
      ∧ ∑' i, m i * (a i - b i - c i) ^ 2
          ≤ 3 * (∑' i, m i * a i ^ 2 + ∑' i, m i * b i ^ 2 + ∑' i, m i * c i ^ 2) := by
  have hpt : ∀ i, m i * (a i - b i - c i) ^ 2 ≤ 3 * (m i * a i ^ 2) + 3 * (m i * b i ^ 2) + 3 * (m i * c i ^ 2) := by
    intro i
    have h3 : (a i - b i - c i) ^ 2 ≤ 3 * (a i ^ 2 + b i ^ 2 + c i ^ 2) := by
      nlinarith [sq_nonneg (a i + b i), sq_nonneg (a i + c i), sq_nonneg (b i - c i)]
    nlinarith [mul_le_mul_of_nonneg_left h3 (hm i)]
  have hsum := ((ha.mul_left 3).add (hb.mul_left 3)).add (hc.mul_left 3)
  have hs : Summable fun i => m i * (a i - b i - c i) ^ 2 :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hm i) (sq_nonneg _)) hpt hsum
  refine ⟨hs, (Summable.tsum_le_tsum hpt hs hsum).trans (le_of_eq ?_)⟩
  rw [Summable.tsum_add ((ha.mul_left 3).add (hb.mul_left 3)) (hc.mul_left 3),
    Summable.tsum_add (ha.mul_left 3) (hb.mul_left 3), tsum_mul_left, tsum_mul_left, tsum_mul_left]
  ring

end Sums

end Cvs.Upstream.ProjectionInterpolantSplit

end

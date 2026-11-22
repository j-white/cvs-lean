import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# A merged lower bound gives positivity, a perpendicular floor, planes and the gap

`Q(r + w) ≥ b‖w‖² + δ·Q(r)` on `R ⊕ (H ∩ Rᗮ)`, with `Q ≥ a‖·‖²` on `D₀` and `R = D₀ ⊔ ℝk`, gives
`Q ≥ 0` on `H` and `Q ≥ min(b, δa)‖·‖²` on `H ∩ k̃ᗮ`, where `k̃ = k − P_{D₀}k`; hence every plane of `H`
carries such a vector, and every eigenvector below `min(b, δa)` satisfies `DavisKahanRayleighRitz`'s gap hypothesis.
-/

noncomputable section

namespace Cvs.Upstream.MergedLowerBoundPositivity

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The merged lower bound: `b‖w‖² + δ·Q(r) ≤ Q(r + w)` for `r ∈ R` and `w ∈ H ∩ Rᗮ`. -/
def Merged (Q : E → ℝ) (H R : Submodule ℝ E) (b δ : ℝ) : Prop :=
  ∀ r ∈ R, ∀ w ∈ H, w ∈ Rᗮ → b * ‖w‖ ^ 2 + δ * Q r ≤ Q (r + w)

/-- At `w = 0` the merged bound makes `Q` nonnegative on `R` when `δ < 1`. -/
theorem nonneg_on_of_merged {Q : E → ℝ} {H R : Submodule ℝ E} {b δ : ℝ}
    (hm : Merged Q H R b δ) (hδ1 : δ < 1) {r : E} (hr : r ∈ R) : 0 ≤ Q r := by
  have h := hm r hr 0 H.zero_mem (Submodule.zero_mem _)
  rw [norm_zero, add_zero] at h
  nlinarith

/-- **The orthogonal split** of a vector of `H` along a subspace `R ≤ H`. -/
theorem exists_split {H R : Submodule ℝ E} [R.HasOrthogonalProjection] (hRH : R ≤ H)
    {f : E} (hf : f ∈ H) :
    ∃ r ∈ R, ∃ w ∈ H, w ∈ Rᗮ ∧ f = r + w ∧ ‖f‖ ^ 2 = ‖r‖ ^ 2 + ‖w‖ ^ 2 := by
  have hPr := R.starProjection_apply_mem f
  have hwR := R.sub_starProjection_mem_orthogonal f
  have hf' : f = R.starProjection f + (f - R.starProjection f) := by abel
  refine ⟨R.starProjection f, hPr, f - R.starProjection f, H.sub_mem hf (hRH hPr), hwR, hf', ?_⟩
  have h0 : ⟪R.starProjection f, f - R.starProjection f⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hPr hwR
  have h := norm_add_sq_real (R.starProjection f) (f - R.starProjection f)
  rw [h0, ← hf'] at h
  linarith

/-- **P1.** A merged bound with `b ≥ 0` and `0 ≤ δ < 1` makes `Q` nonnegative on `H`. -/
theorem nonneg_of_merged {Q : E → ℝ} {H R : Submodule ℝ E} [R.HasOrthogonalProjection]
    {b δ : ℝ} (hm : Merged Q H R b δ) (hRH : R ≤ H) (hb : 0 ≤ b) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {f : E} (hf : f ∈ H) : 0 ≤ Q f := by
  obtain ⟨r, hr, w, hwH, hwR, rfl, -⟩ := exists_split hRH hf
  have h := hm r hr w hwH hwR
  have h1 : 0 ≤ b * ‖w‖ ^ 2 := mul_nonneg hb (sq_nonneg _)
  have h2 : 0 ≤ δ * Q r := mul_nonneg hδ0 (nonneg_on_of_merged hm hδ1 hr)
  linarith

/-- **P3, the gap.** If `⟪T f, f⟫ ≥ μ‖f‖²` whenever `⟪k̃, f⟫ = 0`, every eigenvector `θ ≠ 0` of the
symmetric `T` at `l₁ < μ` satisfies `DavisKahanRayleighRitz`'s `hgap` with `l₂ = μ`. -/
theorem hgap_of_perp {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {kt θ : E} {l₁ μ : ℝ}
    (hθ0 : θ ≠ 0) (hθeig : T θ = l₁ • θ) (hlt : l₁ < μ)
    (hperp : ∀ f : E, ⟪kt, f⟫_ℝ = 0 → μ * ‖f‖ ^ 2 ≤ ⟪T f, f⟫_ℝ) :
    ∀ w : E, ⟪w, θ⟫_ℝ = 0 → μ * ‖w‖ ^ 2 ≤ ⟪T w, w⟫_ℝ := by
  intro w hwθ
  by_contra hcon
  push Not at hcon
  have hθpos : 0 < ‖θ‖ ^ 2 := by positivity
  have hTθθ : ⟪T θ, θ⟫_ℝ = l₁ * ‖θ‖ ^ 2 := by
    rw [hθeig, real_inner_smul_left, real_inner_self_eq_norm_sq]
  by_cases hα : ⟪kt, θ⟫_ℝ = 0
  · have h := hperp θ hα
    rw [hTθθ] at h
    nlinarith
  · set α := ⟪kt, θ⟫_ℝ with hαdef
    set β := ⟪kt, w⟫_ℝ with hβdef
    have hθw : ⟪θ, w⟫_ℝ = 0 := by rw [real_inner_comm]; exact hwθ
    have hTθw : ⟪T θ, w⟫_ℝ = 0 := by rw [hθeig, real_inner_smul_left, hθw, mul_zero]
    have hTwθ : ⟪T w, θ⟫_ℝ = 0 := by rw [hT w θ, hθeig, real_inner_smul_right, hwθ, mul_zero]
    have hku : ⟪kt, α • w - β • θ⟫_ℝ = 0 := by
      rw [inner_sub_right, real_inner_smul_right, real_inner_smul_right]; ring
    have hform : ⟪T (α • w - β • θ), α • w - β • θ⟫_ℝ
        = α ^ 2 * ⟪T w, w⟫_ℝ + β ^ 2 * (l₁ * ‖θ‖ ^ 2) := by
      rw [← hTθθ]
      simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right, hTθw, hTwθ]
      ring
    have hnorm : ‖α • w - β • θ‖ ^ 2 = α ^ 2 * ‖w‖ ^ 2 + β ^ 2 * ‖θ‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq]
      simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
        hwθ, hθw]
      ring
    have h := hperp _ hku
    rw [hform, hnorm] at h
    have hα2 : 0 < α ^ 2 := by positivity
    have h1 : α ^ 2 * ⟪T w, w⟫_ℝ < α ^ 2 * (μ * ‖w‖ ^ 2) := mul_lt_mul_of_pos_left hcon hα2
    have h2 : β ^ 2 * (l₁ * ‖θ‖ ^ 2) ≤ β ^ 2 * (μ * ‖θ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hlt.le hθpos.le) (sq_nonneg β)
    nlinarith

end Cvs.Upstream.MergedLowerBoundPositivity

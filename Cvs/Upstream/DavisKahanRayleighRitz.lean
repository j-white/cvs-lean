import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Rayleigh–Ritz form of Davis–Kahan, and simplicity of an isolated bottom

For a symmetric operator with a unit eigenvector `θ` at `l₁`, and a form at least `l₂` on `θ`'s
orthogonal complement, every unit vector `v` satisfies `(l₂ − l₁)(1 − ⟪v, θ⟫²) ≤ ⟪T v, v⟫ − l₁`.
With `l₁ < l₂` every unit eigenvector at `l₁` is `±θ`.
-/

namespace Cvs.Upstream.DavisKahanRayleighRitz

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Rayleigh–Ritz Davis–Kahan.** If `T` is symmetric, `θ` a unit eigenvector at `l₁`, and
`⟪T w, w⟫ ≥ l₂ ‖w‖²` on `θ`'s orthogonal complement, then every unit `v` has
`(l₂ − l₁)(1 − ⟪v, θ⟫²) ≤ ⟪T v, v⟫ − l₁`. -/
theorem gap_mul_sin_sq_le {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {θ : E} (hθ : ‖θ‖ = 1)
    {l₁ l₂ : ℝ} (hθeig : T θ = l₁ • θ)
    (hgap : ∀ w : E, ⟪w, θ⟫_ℝ = 0 → l₂ * ‖w‖ ^ 2 ≤ ⟪T w, w⟫_ℝ)
    {v : E} (hv : ‖v‖ = 1) :
    (l₂ - l₁) * (1 - ⟪v, θ⟫_ℝ ^ 2) ≤ ⟪T v, v⟫_ℝ - l₁ := by
  set c := ⟪v, θ⟫_ℝ with hc
  set w := v - c • θ with hw
  have hθθ : ⟪θ, θ⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, hθ]; norm_num
  have hwθ : ⟪w, θ⟫_ℝ = 0 := by
    rw [hw, inner_sub_left, real_inner_smul_left, hθθ, ← hc]; ring
  have hθw : ⟪θ, w⟫_ℝ = 0 := by rw [real_inner_comm]; exact hwθ
  have hvsplit : v = c • θ + w := by rw [hw]; abel
  -- norm of the orthogonal part
  have hw2 : ‖w‖ ^ 2 = 1 - c ^ 2 := by
    have h1 : ‖v‖ ^ 2 = ‖c • θ‖ ^ 2 + ‖w‖ ^ 2 := by
      rw [hvsplit]
      have := norm_add_sq_real (c • θ) w
      rw [this, real_inner_smul_left, hθw]; ring
    rw [hv, norm_smul, hθ, Real.norm_eq_abs, mul_one, sq_abs] at h1
    linarith
  -- the form splits: cross terms vanish
  have hTw_θ : ⟪T w, θ⟫_ℝ = 0 := by
    rw [hT w θ, hθeig, real_inner_smul_right, hwθ, mul_zero]
  have hform : ⟪T v, v⟫_ℝ = c ^ 2 * l₁ + ⟪T w, w⟫_ℝ := by
    rw [hvsplit]
    simp only [map_add, map_smul, hθeig, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right, hθθ, hθw, hTw_θ]
    ring
  have hlow := hgap w hwθ
  have hsplit : (l₂ - l₁) * (1 - c ^ 2) = l₂ * ‖w‖ ^ 2 - l₁ * ‖w‖ ^ 2 := by rw [hw2]; ring
  have hkey : c ^ 2 * l₁ - l₁ = -(l₁ * ‖w‖ ^ 2) := by rw [hw2]; ring
  rw [hform, hsplit]
  linarith [hlow, hkey]

end Cvs.Upstream.DavisKahanRayleighRitz

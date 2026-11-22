import Mathlib
import Cvs.L2a.AngularProlateTailPositive
import Cvs.Prolate.CosineTransformSecondOrder
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.SlepianCommutingRelation

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The decay of a rung and of its `u` on `ξ ≥ 1`

From the transform to second order (Cvs.Prolate.CosineTransformSecondOrder): `|ψ(ξ)| ≤ (|A|/c + C₁/c²)/ξ` with `A = g(1) + g(−1)`,
`C₁ = |g₁(1) − g₁(−1)| + ∫|g₂|`, and `|u(ξ)| ≤ (2|A| + C₂/c) ξ` with `C₂ = |h'(1) + h'(−1)| + ∫(2|g₁| + |g₂|)`, for
`c > 0`, `ξ ≥ 1`: the pointwise bounds that make the boundary constant at `b` of the `(1, k)` pairs (Cvs.L2a.TreeBoundFirstPairBoundary) of order
`1/b²`.
-/

namespace Cvs.Prolate.RungDecayBeyondEdge

open Real Set intervalIntegral Cvs.Prolate.SlepianCommutingRelation Cvs.L2a.AngularProlateTailPositive Cvs.Prolate.CosineTransformSecondOrder Cvs.Prolate.Gram.RungGramFloorAtInfinity

variable {g g₁ g₂ : ℝ → ℝ} {c ξ : ℝ}

/-- **The rung decays like `1/ξ`.** -/
theorem abs_psi_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) (hξ : 1 ≤ ξ) :
    |psi c g ξ| ≤ (|g 1 + g (-1)| / c + (|g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s|) / c ^ 2) / ξ := by
  have hξ0 : 0 < ξ := by linarith
  have hcξ : c * ξ ≠ 0 := by positivity
  have h := psi_sub_le hg hg₁ hg₂c hcξ
  set A := g 1 + g (-1) with hA
  set C := |g₁ 1 - g₁ (-1)| + ∫ s in (-1 : ℝ)..1, |g₂ s| with hC
  have hC0 : 0 ≤ C := by
    rw [hC]; exact add_nonneg (abs_nonneg _) (integral_nonneg (by norm_num) fun s _ => abs_nonneg _)
  have h1 : |A * sin (c * ξ) / (c * ξ)| ≤ |A| / (c * ξ) := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < c * ξ)]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)) (by positivity)
  have h2 : C / (c * ξ) ^ 2 ≤ C / c ^ 2 / ξ := by
    rw [div_div]
    apply div_le_div_of_nonneg_left hC0 (by positivity)
    have : ξ ≤ ξ ^ 2 := by nlinarith
    nlinarith [sq_nonneg c]
  calc |psi c g ξ| = |(psi c g ξ - A * sin (c * ξ) / (c * ξ)) + A * sin (c * ξ) / (c * ξ)| := by ring_nf
    _ ≤ |psi c g ξ - A * sin (c * ξ) / (c * ξ)| + |A * sin (c * ξ) / (c * ξ)| := abs_add_le _ _
    _ ≤ C / (c * ξ) ^ 2 + |A| / (c * ξ) := add_le_add h h1
    _ ≤ C / c ^ 2 / ξ + |A| / (c * ξ) := add_le_add h2 le_rfl
    _ = (|A| / c + C / c ^ 2) / ξ := by field_simp; ring

/-- **`u = (ξ² − 1)ψ'` grows at most like `ξ`.** -/
theorem abs_rungU_le (hg : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g (g₁ s) s)
    (hg₁ : ∀ s ∈ uIcc (-1 : ℝ) 1, HasDerivAt g₁ (g₂ s) s) (hg₂c : ContinuousOn g₂ (uIcc (-1) 1))
    (hc : 0 < c) (hξ : 1 ≤ ξ) :
    |rungU c g ξ|
      ≤ (2 * |g 1 + g (-1)| + (|g 1 + g₁ 1 + (g (-1) - g₁ (-1))| + ∫ s in (-1 : ℝ)..1, 2 * |g₁ s| + |g₂ s|) / c) * ξ := by
  have hξ0 : 0 < ξ := by linarith
  have h := u_sub_le hg hg₁ hg₂c hc hξ
  set A := g 1 + g (-1) with hA
  set C₂ := |g 1 + g₁ 1 + (g (-1) - g₁ (-1))| + ∫ s in (-1 : ℝ)..1, 2 * |g₁ s| + |g₂ s| with hC₂
  have hC₂0 : 0 ≤ C₂ := by
    rw [hC₂]
    exact add_nonneg (abs_nonneg _) (integral_nonneg (by norm_num) fun s _ => by positivity)
  have e : rungU c g ξ = (ξ ^ 2 - 1) * kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ := by
    unfold rungU Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval.pP; rfl
  rw [e]
  have h1 : |A * ξ * cos (c * ξ)| ≤ |A| * ξ := by
    rw [abs_mul, abs_mul, abs_of_pos hξ0]
    exact mul_le_of_le_one_right (by positivity) (abs_cos_le_one _)
  have h2 : |A| / ξ ≤ |A| * ξ := by
    rw [div_le_iff₀ hξ0]
    have : (1:ℝ) ≤ ξ * ξ := by nlinarith
    nlinarith [abs_nonneg A]
  have h3 : C₂ / c ≤ C₂ / c * ξ := le_mul_of_one_le_right (by positivity) hξ
  calc |(ξ ^ 2 - 1) * kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ|
      = |((ξ ^ 2 - 1) * kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ - A * ξ * cos (c * ξ))
          + A * ξ * cos (c * ξ)| := by ring_nf
    _ ≤ |(ξ ^ 2 - 1) * kint g (fun ξ s => -(c * s * sin (c * ξ * s))) ξ - A * ξ * cos (c * ξ)|
          + |A * ξ * cos (c * ξ)| := abs_add_le _ _
    _ ≤ (|A| / ξ + C₂ / c) + |A| * ξ := add_le_add h h1
    _ ≤ (|A| * ξ + C₂ / c * ξ) + |A| * ξ := by linarith
    _ = (2 * |A| + C₂ / c) * ξ := by ring

end Cvs.Prolate.RungDecayBeyondEdge

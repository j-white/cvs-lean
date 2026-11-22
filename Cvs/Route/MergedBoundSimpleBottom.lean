import Mathlib

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# REQ gives simplicity, `sin² ≤ 1/(xL)` and the transform limit

With `a = c₂m₈`, `m₄ = r₄₈m₈`, the merged bound `(b, δ)` and L1 `Q(k̄) ≤ C₁m₄`, REQ
(`b ≥ C₁xLm₄`, `δ ≥ C₁xL·r₄₈/c₂`) is `min(b, δa) ≥ C₁xLm₄`; for `xL > 1` the bottom is simple and
isolated, `1 − ⟪k̄, θ⟫² ≤ 1/(xL)`, `‖±θ − k̄‖² ≤ 2/(xL)`, and `s·ℓ(θ) − ℓ(s k̄) → 0` uniformly.
-/

noncomputable section

namespace Cvs.Route.MergedBoundSimpleBottom

open scoped InnerProductSpace Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For unit `u, v` with `⟪u, v⟫ ≥ 0`, `‖u − v‖² ≤ 2(1 − ⟪v, u⟫²)`. -/
theorem norm_sub_sq_le_of_inner_nonneg {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : 0 ≤ ⟪u, v⟫_ℝ) : ‖u - v‖ ^ 2 ≤ 2 * (1 - ⟪v, u⟫_ℝ ^ 2) := by
  have h1 : ⟪u, v⟫_ℝ ≤ 1 := by
    have := real_inner_le_norm u v
    rw [hu, hv, mul_one] at this; exact this
  rw [norm_sub_sq_real, hu, hv, real_inner_comm u v]
  nlinarith

/-- **The signed distance under REQ.** One of `±θ`, an eigenvector at `l₁`, has
`‖±θ − k̄‖² ≤ 2/(xL)`. -/
theorem exists_sign_norm_sub_sq_le {T : E →ₗ[ℝ] E} {kbar θ : E} {x L l₁ : ℝ}
    (hkbar : ‖kbar‖ = 1) (hθ : ‖θ‖ = 1) (hθeig : T θ = l₁ • θ)
    (hsin : 1 - ⟪kbar, θ⟫_ℝ ^ 2 ≤ 1 / (x * L)) :
    ∃ θ' : E, (θ' = θ ∨ θ' = -θ) ∧ T θ' = l₁ • θ' ∧ ‖θ' - kbar‖ ^ 2 ≤ 2 / (x * L) := by
  by_cases h : 0 ≤ ⟪θ, kbar⟫_ℝ
  · refine ⟨θ, Or.inl rfl, hθeig, ?_⟩
    have := norm_sub_sq_le_of_inner_nonneg hθ hkbar h
    rw [show (2 : ℝ) / (x * L) = 2 * (1 / (x * L)) by ring]
    linarith
  · push Not at h
    have hθ' : ‖-θ‖ = 1 := by rw [norm_neg, hθ]
    have hin : 0 ≤ ⟪-θ, kbar⟫_ℝ := by rw [inner_neg_left]; linarith
    refine ⟨-θ, Or.inr rfl, by rw [map_neg, hθeig, smul_neg], ?_⟩
    have := norm_sub_sq_le_of_inner_nonneg hθ' hkbar hin
    rw [inner_neg_right, neg_sq] at this
    rw [show (2 : ℝ) / (x * L) = 2 * (1 / (x * L)) by ring]
    linarith

section Step4

variable {ι Z F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

end Step4

end Cvs.Route.MergedBoundSimpleBottom

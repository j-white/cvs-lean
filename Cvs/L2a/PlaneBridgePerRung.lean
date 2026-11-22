import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The plane bridge's ρ from per-rung pairing bounds

The edge sum of `Φ = Σⱼ aⱼψⱼ` pairs with a profile `vᵢ` through the per-rung pairings `Pⱼᵢ`: `⟨F_e, vᵢ⟩ = Σⱼ aⱼPⱼᵢ`.
By Cauchy–Schwarz with positive rung weights `Dⱼ`, `Σᵢ⟨F_e, vᵢ⟩² ≤ (Σⱼ aⱼ²Dⱼ)·Σᵢⱼ Pⱼᵢ²/Dⱼ`, and a frame bound
`λΣⱼ aⱼ²Dⱼ ≤ ‖F_e‖²` gives the hypothesis `Σᵢ⟨F_e, vᵢ⟩² ≤ ρ²‖F_e‖²` of Cvs.L2a.PlaneBridgePlateau with `ρ² = (Σᵢⱼ eⱼᵢ²/Dⱼ)/λ` for any
bounds `|Pⱼᵢ| ≤ eⱼᵢ`: the certified per-rung pairings enter the plateau through a finite double sum.
-/

namespace Cvs.L2a.PlaneBridgePerRung

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **Cauchy–Schwarz with weights**: `(Σⱼ aⱼPⱼ)² ≤ (Σⱼ aⱼ²Dⱼ)(Σⱼ Pⱼ²/Dⱼ)` for positive `D`. -/
theorem sq_sum_le_weighted (a P D : ι → ℝ) (hD : ∀ j, 0 < D j) :
    (∑ j, a j * P j) ^ 2 ≤ (∑ j, a j ^ 2 * D j) * ∑ j, P j ^ 2 / D j := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun j => a j * Real.sqrt (D j))
    (fun j => P j / Real.sqrt (D j))
  have e1 : ∀ j, a j * Real.sqrt (D j) * (P j / Real.sqrt (D j)) = a j * P j := fun j => by
    have := Real.sqrt_pos.mpr (hD j); field_simp
  have e2 : ∀ j, (a j * Real.sqrt (D j)) ^ 2 = a j ^ 2 * D j := fun j => by
    rw [mul_pow, Real.sq_sqrt (hD j).le]
  have e3 : ∀ j, (P j / Real.sqrt (D j)) ^ 2 = P j ^ 2 / D j := fun j => by
    rw [div_pow, Real.sq_sqrt (hD j).le]
  simp only [e1, e2, e3] at h
  exact h

end Cvs.L2a.PlaneBridgePerRung

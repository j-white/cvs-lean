import Mathlib
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rung Gram floor from the certified per-rung quantities

With `A = cb√(b² − 1)`, every rung has `Aψ_i(b)² + u_i(b)²/A ≤ (b/√(b² − 1)) E_i(b)` (its amplitude `a_i(b)` lies in
`[c(b² − 1), cb√(b² − 1)]`), and its mass from the edge point `ξ₀` is at least `∫_{ξ₀}^b E_i/(2a_i) − G_i/(2q_i(ξ₀))`
(Cvs.Prolate.ProlateMassEnergyWeighted); so an earlier result gives `∫₁ᵇ (Σ a_iψ_i)² ≥ Σ_i a_i² (∫_{ξ₀}^b E_i/(2a_i) − G_i/(2q_i(ξ₀)) − (26/5)(b/√(b² − 1)) E_i(b)/δ_i)`.
-/

noncomputable section

namespace Cvs.Prolate.Gram.RungGramFloorPerRung

open Real Set Finset Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **`Aψ(b)² + u(b)²/A ≤ (b/√(b² − 1)) E(b)`** at `A = cb√(b² − 1)`, for `χ < c²`, `b > 1`. -/
theorem bracket_le {c χ b : ℝ} {ψ u : ℝ → ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχ : χ < c ^ 2) (hb : 1 < b) :
    c * b * √(b ^ 2 - 1) * ψ b ^ 2 + u b ^ 2 / (c * b * √(b ^ 2 - 1))
      ≤ b / √(b ^ 2 - 1) * energy (aP c χ) ψ u b := by
  have hb2 : 0 < b ^ 2 - 1 := by nlinarith
  have hs : 0 < √(b ^ 2 - 1) := sqrt_pos.mpr hb2
  have hss : √(b ^ 2 - 1) ^ 2 = b ^ 2 - 1 := sq_sqrt hb2.le
  set A := c * b * √(b ^ 2 - 1) with hA
  have hA0 : 0 < A := by positivity
  have ha0 : 0 < aP c χ b := aP_pos hb (by positivity) hχ
  -- `a(b)² = (b² − 1)(c²b² − χ) ≤ A²` and `A² ≤ (b²/(b² − 1)) a(b)²`
  have hasq : aP c χ b ^ 2 = (b ^ 2 - 1) * (c ^ 2 * b ^ 2 - χ) := by
    rw [aP_sq hb (by positivity) hχ]; unfold pP qP; ring
  have hA2 : A ^ 2 = c ^ 2 * b ^ 2 * (b ^ 2 - 1) := by rw [hA, mul_pow, hss]; ring
  have h1 : aP c χ b ≤ A := by
    apply le_of_sq_le_sq _ hA0.le
    rw [hasq, hA2]; nlinarith
  have h2 : A * √(b ^ 2 - 1) ≤ b * aP c χ b := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, hss, hA2, mul_pow, hasq]
    have : c ^ 2 * b ^ 2 - χ ≥ c ^ 2 * b ^ 2 - c ^ 2 := by linarith
    nlinarith [mul_pos hb2 (by positivity : (0:ℝ) < c ^ 2), sq_nonneg b, hb2]
  unfold energy
  set ρ := b / √(b ^ 2 - 1) with hρ
  have hρ1 : 1 ≤ ρ := by
    rw [hρ, le_div_iff₀ hs]; rw [one_mul]
    exact le_of_sq_le_sq (by rw [hss]; linarith) (by linarith)
  -- `A ≤ ρ a(b)` and `a(b) ≤ A ≤ ρ A`
  have hAρ : A ≤ ρ * aP c χ b := by
    rw [hρ, div_mul_eq_mul_div, le_div_iff₀ hs]; linarith [h2]
  calc A * ψ b ^ 2 + u b ^ 2 / A
      ≤ ρ * aP c χ b * ψ b ^ 2 + ρ * (u b ^ 2 / aP c χ b) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right hAρ (sq_nonneg _)
        · calc u b ^ 2 / A ≤ u b ^ 2 / aP c χ b := div_le_div_of_nonneg_left (sq_nonneg _) ha0 h1
            _ ≤ ρ * (u b ^ 2 / aP c χ b) := le_mul_of_one_le_left (by positivity) hρ1
    _ = ρ * (aP c χ b * ψ b ^ 2 + u b ^ 2 / aP c χ b) := by ring

end Cvs.Prolate.Gram.RungGramFloorPerRung

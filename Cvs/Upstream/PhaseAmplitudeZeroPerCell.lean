import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Topology.Order.IntermediateValue

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Zeros of a phase-amplitude pair, one per cell

If `Y = A(cos ϑ + r₀)` and `Y' = B(−sin ϑ + r₁)` with `A, B > 0`, `|r₀| < ρ₀`, `|r₁| ≤ ρ₁`, `ρ₀² + ρ₁² < 1`, then
every zero has `ϑ` within `arcsin ρ₀` of `π/2 + πℤ`, each cell `ϑ ∈ π/2 + nπ ± arcsin ρ₀` holds exactly one zero,
and a Robin point `Y' = λY` has `|sin ϑ| ≤ |r₁| + |λ|(A/B)(1 + |r₀|)`.
-/

noncomputable section

open Real Set

namespace Cvs.Upstream.PhaseAmplitudeZeroPerCell

/-! ### Trigonometric bookkeeping -/

/-- `|(−1)ⁿ| = 1`. -/
theorem abs_neg_one_zpow (n : ℤ) : |((-1 : ℝ) ^ n)| = 1 := by
  rw [abs_zpow, abs_neg, abs_one, one_zpow]

/-- `((−1)ⁿ)² = 1`. -/
theorem neg_one_zpow_sq (n : ℤ) : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
  rw [← sq_abs, abs_neg_one_zpow, one_pow]

/-- `cos θ = −(−1)ⁿ sin(θ − (π/2 + nπ))`. -/
theorem cos_eq_neg_sign_mul_sin (θ : ℝ) (n : ℤ) : cos θ = -((-1) ^ n * sin (θ - (π / 2 + n * π))) := by
  rw [show θ - (π / 2 + n * π) = (θ - π / 2) - n * π by ring, sin_sub_int_mul_pi, sin_sub_pi_div_two]
  linear_combination (-cos θ) * neg_one_zpow_sq n

/-- On `[−π/2, π/2]`, `|d| ≤ arcsin β` when `|sin d| ≤ β`. -/
theorem abs_le_arcsin_of_abs_sin_le {d β : ℝ} (hd : |d| ≤ π / 2) (h : |sin d| ≤ β) :
    |d| ≤ arcsin β := by
  have hs : sin |d| = |sin d| := by
    rcases le_total 0 d with h0 | h0
    · rw [abs_of_nonneg h0, abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [abs_le.mp hd]))]
    · rw [abs_of_nonpos h0, sin_neg, abs_of_nonpos (sin_nonpos_of_nonpos_of_neg_pi_le h0
        (by linarith [abs_le.mp hd, pi_pos]))]
  have h1 : arcsin (sin |d|) = |d| := arcsin_sin (by linarith [abs_nonneg d, pi_pos]) hd
  rw [← h1, hs]
  exact arcsin_le_arcsin h

/-- Every real lies within `π/2` of `π/2 + nπ` for `n = ⌊θ/π⌋`. -/
theorem abs_sub_floor_le (θ : ℝ) : |θ - (π / 2 + ⌊θ / π⌋ * π)| ≤ π / 2 := by
  have h1 := Int.floor_le (θ / π)
  have h2 := Int.lt_floor_add_one (θ / π)
  have hp := pi_pos
  have e1 : (⌊θ / π⌋ : ℝ) * π ≤ θ := by rwa [le_div_iff₀ hp] at h1
  have e2 : θ < ((⌊θ / π⌋ : ℝ) + 1) * π := by rwa [div_lt_iff₀ hp] at h2
  rw [abs_le]; constructor <;> nlinarith

/-! ### Lemma Z -/

/-! ### Lemma Z′ -/

end Cvs.Upstream.PhaseAmplitudeZeroPerCell

import Mathlib
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.RungFrequencyWindow
import Cvs.Upstream.SturmLiouvillePrufer

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The phase rates of a rung dilate against a profile

The pairing of a rung's mode `ψ(m·)` with the profile `cos(cm′·)` carries the phases `Θ(mθ) ∓ cm′θ`, with rates
`m Θ'(mθ) ∓ cm′`. Beyond `mθ ≥ ξ₀ > 1` the rate window of Cvs.Prolate.LiouvilleGreen.RungFrequencyWindow gives `c m (1 − ξ₀/(c(ξ₀² − 1))) ≤ m Θ'(mθ) ≤ c m U(ξ₀)`,
`U(ξ) = ξ/√(ξ² − 1) · (1 + ξ/(c(ξ² − 1)))`, so the difference phase has no stationary point when `m′ > m U(ξ₀)` and
the first-derivative test of Cvs.Upstream.FirstDerivativeTestVariation applies to both phases.
-/

namespace Cvs.Prolate.LiouvilleGreen.DilatedPhaseRates

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Upstream.SturmLiouvillePrufer Cvs.Prolate.LiouvilleGreen.RungFrequencyWindow

/-- The frequency envelope `U(ξ) = ξ/√(ξ² − 1) · (1 + ξ/(c(ξ² − 1)))`. -/
noncomputable def U (c ξ : ℝ) : ℝ := ξ / √(ξ ^ 2 - 1) * (1 + ξ / (c * (ξ ^ 2 - 1)))

/-- `U` is antitone on `(1, ∞)`: both factors decrease. -/
theorem U_antitone {c ξ₀ ξ : ℝ} (hc : 0 < c) (h0 : 1 < ξ₀) (hξ : ξ₀ ≤ ξ) : U c ξ ≤ U c ξ₀ := by
  unfold U
  have h1 : (0 : ℝ) < ξ₀ ^ 2 - 1 := by nlinarith
  have h2 : (0 : ℝ) < ξ ^ 2 - 1 := by nlinarith
  have hξ1 : 1 < ξ := lt_of_lt_of_le h0 hξ
  -- `ξ/√(ξ² − 1)` decreases: its square `ξ²/(ξ² − 1) = 1 + 1/(ξ² − 1)`
  have hA : ξ / √(ξ ^ 2 - 1) ≤ ξ₀ / √(ξ₀ ^ 2 - 1) := by
    have hs : (ξ / √(ξ ^ 2 - 1)) ^ 2 ≤ (ξ₀ / √(ξ₀ ^ 2 - 1)) ^ 2 := by
      rw [div_pow, div_pow, sq_sqrt h2.le, sq_sqrt h1.le]
      rw [div_le_div_iff₀ h2 h1]
      nlinarith
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hs
  -- `ξ/(c(ξ² − 1))` decreases
  have hB : ξ / (c * (ξ ^ 2 - 1)) ≤ ξ₀ / (c * (ξ₀ ^ 2 - 1)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hc.le (mul_nonneg (sub_nonneg.mpr hξ) (by positivity : (0 : ℝ) ≤ ξ * ξ₀ + 1))]
  have hA0 : 0 ≤ ξ / √(ξ ^ 2 - 1) := by positivity
  have hB0 : 0 ≤ 1 + ξ / (c * (ξ ^ 2 - 1)) := by positivity
  calc ξ / √(ξ ^ 2 - 1) * (1 + ξ / (c * (ξ ^ 2 - 1)))
      ≤ ξ₀ / √(ξ₀ ^ 2 - 1) * (1 + ξ / (c * (ξ ^ 2 - 1))) := mul_le_mul_of_nonneg_right hA hB0
    _ ≤ ξ₀ / √(ξ₀ ^ 2 - 1) * (1 + ξ₀ / (c * (ξ₀ ^ 2 - 1))) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **The rate of a dilated rung is pinned to `c m`**: for `mθ ≥ ξ₀ > 1`,
`c m (1 − ξ₀/(c(ξ₀² − 1))) ≤ m Θ'(mθ) ≤ c m U(ξ₀)`. -/
theorem dilate_rate_bounds {c χ ξ₀ θ : ℝ} {m : ℕ} {ψ u : ℝ → ℝ} (hm : 1 ≤ m) (h0 : 1 < ξ₀)
    (hθ : ξ₀ ≤ m * θ) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hs : ξ₀ / (c * (ξ₀ ^ 2 - 1)) ≤ 1)
    (hE : 0 < energy (aP c χ) ψ u (m * θ)) :
    c * m * (1 - ξ₀ / (c * (ξ₀ ^ 2 - 1))) ≤ m * rate pP (aP c χ) (wP c χ) (qP c χ) ψ u (m * θ)
      ∧ m * rate pP (aP c χ) (wP c χ) (qP c χ) ψ u (m * θ) ≤ c * m * U c ξ₀ := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hξ : 1 < (m : ℝ) * θ := lt_of_lt_of_le h0 hθ
  obtain ⟨hlo, hhi⟩ := rate_bounds (ψ := ψ) (u := u) hξ hc hχ0 hχc hE
  obtain ⟨hfl, hfh⟩ := freq_bounds (χ := χ) hξ hc hχ0 hχc
  have h1 : (0 : ℝ) < (m * θ) ^ 2 - 1 := by nlinarith
  have h0' : (0 : ℝ) < ξ₀ ^ 2 - 1 := by nlinarith
  -- the correction decreases in `ξ`
  have hcorr : (m : ℝ) * θ / (c * ((m * θ) ^ 2 - 1)) ≤ ξ₀ / (c * (ξ₀ ^ 2 - 1)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg hc.le (mul_nonneg (sub_nonneg.mpr hθ) (by positivity : (0 : ℝ) ≤ m * θ * ξ₀ + 1))]
  constructor
  · calc c * m * (1 - ξ₀ / (c * (ξ₀ ^ 2 - 1)))
        ≤ c * m * (1 - m * θ / (c * ((m * θ) ^ 2 - 1))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ ≤ m * (aP c χ (m * θ) / pP (m * θ) * (1 - m * θ / (c * ((m * θ) ^ 2 - 1)))) := by
          have : c * (1 - m * θ / (c * ((m * θ) ^ 2 - 1)))
              ≤ aP c χ (m * θ) / pP (m * θ) * (1 - m * θ / (c * ((m * θ) ^ 2 - 1))) :=
            mul_le_mul_of_nonneg_right hfl.le (by linarith)
          nlinarith
      _ ≤ m * rate pP (aP c χ) (wP c χ) (qP c χ) ψ u (m * θ) :=
          mul_le_mul_of_nonneg_left hlo hm0.le
  · calc (m : ℝ) * rate pP (aP c χ) (wP c χ) (qP c χ) ψ u (m * θ)
        ≤ m * (aP c χ (m * θ) / pP (m * θ) * (1 + m * θ / (c * ((m * θ) ^ 2 - 1)))) :=
          mul_le_mul_of_nonneg_left hhi hm0.le
      _ ≤ m * (c * (m * θ) / √((m * θ) ^ 2 - 1) * (1 + m * θ / (c * ((m * θ) ^ 2 - 1)))) := by
          apply mul_le_mul_of_nonneg_left _ hm0.le
          exact mul_le_mul_of_nonneg_right hfh (by positivity)
      _ = c * m * U c (m * θ) := by unfold U; ring
      _ ≤ c * m * U c ξ₀ := mul_le_mul_of_nonneg_left (U_antitone hc h0 hθ) (by positivity)

end Cvs.Prolate.LiouvilleGreen.DilatedPhaseRates

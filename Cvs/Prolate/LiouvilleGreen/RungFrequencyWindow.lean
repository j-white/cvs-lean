import Mathlib
import Cvs.Prolate.Gram.RungGramFloorAtInfinity
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.PruferRateFrequency
import Cvs.Upstream.SturmLiouvillePrufer

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The frequency window of a prolate rung beyond the edge

The local frequency `a/p = √((c²ξ² − χ)/(ξ² − 1))` of a rung with `0 ≤ χ < c²` satisfies
`c < a/p ≤ c ξ/√(ξ² − 1)` for `ξ > 1`, and with `w ≤ 2ξ/(c(ξ² − 1))` the Prüfer rate lies in
`[c − ξ/(ξ² − 1), c ξ/√(ξ² − 1) · (1 + ξ/(c(ξ² − 1)))]`: beyond `ξ = k` every rung's phase runs at the frequency `c`
within the relative error `1/√(1 − 1/k²) − 1 + 1/(c(k − 1))`, the separation the profile pairings use.
-/

namespace Cvs.Prolate.LiouvilleGreen.RungFrequencyWindow

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.Gram.RungGramFloorAtInfinity Cvs.Upstream.SturmLiouvillePrufer Cvs.Prolate.LiouvilleGreen.PruferRateFrequency

/-- The squared frequency: `(a/p)² = c² + (c² − χ)/(ξ² − 1)`. -/
theorem freq_sq {c χ ξ : ℝ} (hξ : 1 < ξ) (hc : 0 < c) (_hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    (aP c χ ξ / pP ξ) ^ 2 = c ^ 2 + (c ^ 2 - χ) / (ξ ^ 2 - 1) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hp : 0 < pP ξ := pP_pos hξ
  have hq : 0 < qP c χ ξ := qP_pos hξ hc2 hχc
  rw [div_pow, aP_sq hξ hc2 hχc]
  unfold pP qP
  have h1 : (0 : ℝ) < ξ ^ 2 - 1 := by nlinarith
  field_simp
  ring

/-- **The frequency window**: `c < a/p` and `a/p ≤ c ξ/√(ξ² − 1)`. -/
theorem freq_bounds {c χ ξ : ℝ} (hξ : 1 < ξ) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    c < aP c χ ξ / pP ξ ∧ aP c χ ξ / pP ξ ≤ c * ξ / √(ξ ^ 2 - 1) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hp : 0 < pP ξ := pP_pos hξ
  have ha : 0 < aP c χ ξ := aP_pos hξ hc2 hχc
  have hpos : 0 < aP c χ ξ / pP ξ := div_pos ha hp
  have h1 : (0 : ℝ) < ξ ^ 2 - 1 := by nlinarith
  have hsq := freq_sq hξ hc hχ0 hχc
  constructor
  · have : c ^ 2 < (aP c χ ξ / pP ξ) ^ 2 := by
      rw [hsq]
      have : 0 < (c ^ 2 - χ) / (ξ ^ 2 - 1) := div_pos (by linarith) h1
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 hpos.le this
  · have hle : (aP c χ ξ / pP ξ) ^ 2 ≤ (c * ξ / √(ξ ^ 2 - 1)) ^ 2 := by
      rw [hsq, div_pow, sq_sqrt h1.le]
      rw [le_div_iff₀ h1]
      have : (c ^ 2 - χ) / (ξ ^ 2 - 1) * (ξ ^ 2 - 1) = c ^ 2 - χ := by field_simp
      nlinarith [this, hχ0]
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hle

/-- **The rate window of a prolate rung**: with the rung's energy positive at `ξ`, the Prüfer rate is the frequency
`a/p` within the relative error `ξ/(c(ξ² − 1))`, and `c < a/p ≤ c ξ/√(ξ² − 1)`. -/
theorem rate_bounds {c χ ξ : ℝ} {ψ u : ℝ → ℝ} (hξ : 1 < ξ) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hE : 0 < energy (aP c χ) ψ u ξ) :
    aP c χ ξ / pP ξ * (1 - ξ / (c * (ξ ^ 2 - 1))) ≤ rate pP (aP c χ) (wP c χ) (qP c χ) ψ u ξ
      ∧ rate pP (aP c χ) (wP c χ) (qP c χ) ψ u ξ ≤ aP c χ ξ / pP ξ * (1 + ξ / (c * (ξ ^ 2 - 1))) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have hp : 0 < pP ξ := pP_pos hξ
  have ha : 0 < aP c χ ξ := aP_pos hξ hc2 hχc
  have h1 : (0 : ℝ) < ξ ^ 2 - 1 := by nlinarith
  have hw0 : 0 < wP c χ ξ := wP_pos hξ hc2 hχc
  have hwle : wP c χ ξ ≤ 2 * ξ / (c * pP ξ) := wP_le_far hξ hc hχ0 hχc
  have hkey := abs_rate_sub_le (p := pP) (a := aP c χ) (w := wP c χ) (q := qP c χ) (ψ := ψ) (u := u)
    ha hp (aP_sq hξ hc2 hχc) hE
  rw [abs_of_pos hw0] at hkey
  have hfreq : 0 < aP c χ ξ / pP ξ := div_pos ha hp
  have hpP : pP ξ = ξ ^ 2 - 1 := rfl
  have hcorr : wP c χ ξ * (aP c χ ξ / pP ξ) / 2 ≤ (aP c χ ξ / pP ξ) * (ξ / (c * (ξ ^ 2 - 1))) := by
    rw [hpP] at hwle
    calc wP c χ ξ * (aP c χ ξ / pP ξ) / 2 ≤ 2 * ξ / (c * (ξ ^ 2 - 1)) * (aP c χ ξ / pP ξ) / 2 := by
          gcongr
      _ = (aP c χ ξ / pP ξ) * (ξ / (c * (ξ ^ 2 - 1))) := by ring
  have := abs_le.mp hkey
  constructor <;> nlinarith [this.1, this.2, hcorr]

end Cvs.Prolate.LiouvilleGreen.RungFrequencyWindow

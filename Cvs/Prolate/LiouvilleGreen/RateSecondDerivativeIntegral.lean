import Mathlib
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The integral of the rate's second derivative, in closed form

On `[p, q]` beyond the edge the rate's derivative is `freq' + corr'` (Cvs.Prolate.LiouvilleGreen.PruferRateDerivative); the frequency's share integrates
exactly to `(a/p)(p) − (a/p)(q)` (Cvs.Prolate.LiouvilleGreen.FrequencyVariation) and the correction's share is pointwise at most a constant built from the
monotone coefficient bounds (`a`, `q`, `dP` increasing, `w ≤ 2p/(c(p² − 1))`, `|w'|` by Cvs.Prolate.LiouvilleGreen.RateDerivativeSize), so
`∫_p^q |Θ''| ≤ (a/p)(p) − (a/p)(q) + (q − p)·C(p, q)`: the last datum of the envelopes of Cvs.Prolate.LiouvilleGreen.FirstModeProfileEnvelope and an earlier result in closed form.
-/

namespace Cvs.Prolate.LiouvilleGreen.RateSecondDerivativeIntegral

open Real Set MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-- `a` increases on `(1, ∞)`. -/
theorem aP_mono {c χ p t : ℝ} (hp : 1 < p) (hpt : p ≤ t) (hc : 0 < c) (_hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    aP c χ p ≤ aP c χ t := by
  have hc2 : 0 < c ^ 2 := by positivity
  unfold aP pP qP
  apply Real.sqrt_le_sqrt
  have hp2 : (1 : ℝ) ≤ p ^ 2 := by nlinarith
  have hpt2 : p ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by linarith) hpt 2
  have h0 : (0 : ℝ) ≤ c ^ 2 * p ^ 2 - χ := by nlinarith [mul_le_mul_of_nonneg_left hp2 hc2.le]
  have h2' : c ^ 2 * p ^ 2 - χ ≤ c ^ 2 * t ^ 2 - χ := by nlinarith [mul_le_mul_of_nonneg_left hpt2 hc2.le]
  exact mul_le_mul (by nlinarith) h2' h0 (by nlinarith)

end Cvs.Prolate.LiouvilleGreen.RateSecondDerivativeIntegral

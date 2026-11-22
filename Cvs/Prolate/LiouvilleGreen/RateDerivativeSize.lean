import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The size of the derivative of the Liouville–Green rate

The rate `w = (pq)'/(2qa)` of a prolate rung has the nonpositive derivative `w'` of Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval; dropping the positive
term of the quotient rule, `|w'| ≤ dP (2c²ξ a + w q²)/(2 q² a²)` with `dP = (pq)' = 2ξ(2c²ξ² − c² − χ)`: the last
coefficient datum of the tests, so that `∫|φ''|` of a profile pairing is a closed form through Cvs.Prolate.LiouvilleGreen.FrequencyVariation and an earlier result.
-/

namespace Cvs.Prolate.LiouvilleGreen.RateDerivativeSize

open Real Set Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-- **The derivative of `w` is bounded**: `|w'| ≤ dP (2c²ξ a + w q²)/(2 q² a²)` for `ξ > 1`, `0 ≤ χ < c²`. -/
theorem abs_wP'_le {c χ ξ : ℝ} (hξ : 1 < ξ) (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    |wP' c χ ξ| ≤ dP c χ ξ * (2 * c ^ 2 * ξ * aP c χ ξ + wP c χ ξ * qP c χ ξ ^ 2)
      / (2 * qP c χ ξ ^ 2 * aP c χ ξ ^ 2) := by
  have hc2 : 0 < c ^ 2 := by positivity
  have ha := aP_pos hξ hc2 hχc
  have hq := qP_pos hξ hc2 hχc
  have hw := wP_pos hξ hc2 hχc
  have hd := dP_pos hξ hc2 hχc
  have hneg := wP'_nonpos hξ hc2 hχ0 hχc
  rw [abs_of_nonpos hneg]
  unfold wP'
  have hξ0 : 0 < ξ := by linarith
  have hpos : 0 ≤ 2 * (6 * c ^ 2 * ξ ^ 2 - c ^ 2 - χ) * (2 * qP c χ ξ * aP c χ ξ) := by
    have : 0 ≤ 6 * c ^ 2 * ξ ^ 2 - c ^ 2 - χ := by
      nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ ξ ^ 2 by nlinarith) hc2.le]
    positivity
  rw [← neg_div, neg_sub]
  have hden : 0 < (2 * qP c χ ξ * aP c χ ξ) ^ 2 := by positivity
  calc (dP c χ ξ * (2 * (2 * c ^ 2 * ξ * aP c χ ξ + qP c χ ξ * (wP c χ ξ * qP c χ ξ)))
        - 2 * (6 * c ^ 2 * ξ ^ 2 - c ^ 2 - χ) * (2 * qP c χ ξ * aP c χ ξ)) / (2 * qP c χ ξ * aP c χ ξ) ^ 2
      ≤ dP c χ ξ * (2 * (2 * c ^ 2 * ξ * aP c χ ξ + qP c χ ξ * (wP c χ ξ * qP c χ ξ)))
        / (2 * qP c χ ξ * aP c χ ξ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ hden.le
        linarith
    _ = dP c χ ξ * (2 * c ^ 2 * ξ * aP c χ ξ + wP c χ ξ * qP c χ ξ ^ 2)
        / (2 * qP c χ ξ ^ 2 * aP c χ ξ ^ 2) := by
        field_simp

end Cvs.Prolate.LiouvilleGreen.RateDerivativeSize

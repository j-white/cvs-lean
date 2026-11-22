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
# The Liouville–Green rate near the edge

The rate `w = (pq)'/(2qa)` of a prolate rung is exactly `ξ/a + ξc²(ξ² − 1)/(qa)`, and since `q = c²(ξ² − 1) + c² − χ`
dominates `c²(ξ² − 1)`, `w ≤ 2ξ/a ≤ 2ξ/(cσ√(ξ² − 1))` with `σ² = (c² − χ)/c²`. The condition `w(ξ₀) < 2` of the
energy bounds then holds from `ξ₀² − 1 ≈ 1/(c²σ²)`, the Bessel-layer scale, instead of `ξ₀ − 1 ≈ 1/(2c)`.
-/

namespace Cvs.Prolate.LiouvilleGreen.RateNearEdge

open Real Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-- **The rate, exactly**: `w = ξ/a + ξc²(ξ² − 1)/(qa)`. -/
theorem wP_eq {c χ ξ : ℝ} (hξ : 1 < ξ) (hc2 : 0 < c ^ 2) (hχc : χ < c ^ 2) :
    wP c χ ξ = ξ / aP c χ ξ + ξ * c ^ 2 * (ξ ^ 2 - 1) / (qP c χ ξ * aP c χ ξ) := by
  have ha := aP_pos hξ hc2 hχc
  have hq := qP_pos hξ hc2 hχc
  unfold wP dP
  have e : (2 * c ^ 2 * ξ ^ 2 - c ^ 2 - χ) = qP c χ ξ + c ^ 2 * (ξ ^ 2 - 1) := by unfold qP; ring
  rw [e]
  field_simp

/-- **The rate is at most `2ξ/a`.** -/
theorem wP_le_two_div_a {c χ ξ : ℝ} (hξ : 1 < ξ) (hc2 : 0 < c ^ 2) (hχc : χ < c ^ 2) :
    wP c χ ξ ≤ 2 * ξ / aP c χ ξ := by
  have ha := aP_pos hξ hc2 hχc
  have hq := qP_pos hξ hc2 hχc
  have hξ0 : 0 < ξ := by linarith
  rw [wP_eq hξ hc2 hχc]
  have hdom : c ^ 2 * (ξ ^ 2 - 1) ≤ qP c χ ξ := by unfold qP; linarith
  have h2 : ξ * c ^ 2 * (ξ ^ 2 - 1) / (qP c χ ξ * aP c χ ξ) ≤ ξ / aP c χ ξ := by
    rw [div_le_div_iff₀ (mul_pos hq ha) ha]
    have : ξ * c ^ 2 * (ξ ^ 2 - 1) * aP c χ ξ ≤ ξ * (qP c χ ξ * aP c χ ξ) := by
      have := mul_le_mul_of_nonneg_left hdom (mul_nonneg hξ0.le ha.le)
      nlinarith [this]
    exact this
  calc ξ / aP c χ ξ + ξ * c ^ 2 * (ξ ^ 2 - 1) / (qP c χ ξ * aP c χ ξ)
      ≤ ξ / aP c χ ξ + ξ / aP c χ ξ := by linarith
    _ = 2 * ξ / aP c χ ξ := by ring

/-- **The rate near the edge**: `w ≤ 2ξ/√((ξ² − 1)(c² − χ))`. -/
theorem wP_le_edge {c χ ξ : ℝ} (hξ : 1 < ξ) (hc2 : 0 < c ^ 2) (hχc : χ < c ^ 2) :
    wP c χ ξ ≤ 2 * ξ / √((ξ ^ 2 - 1) * (c ^ 2 - χ)) := by
  refine (wP_le_two_div_a hξ hc2 hχc).trans ?_
  have hξ0 : 0 < ξ := by linarith
  have h1 : 0 < ξ ^ 2 - 1 := by nlinarith
  have hpos : 0 < √((ξ ^ 2 - 1) * (c ^ 2 - χ)) := Real.sqrt_pos.mpr (mul_pos h1 (by linarith))
  apply div_le_div_of_nonneg_left (by positivity) hpos
  unfold aP pP qP
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ h1.le
  nlinarith

end Cvs.Prolate.LiouvilleGreen.RateNearEdge

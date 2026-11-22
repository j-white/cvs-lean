import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Prolate.LiouvilleGreen.PruferRateFrequency
import Cvs.Prolate.LiouvilleGreen.RateNearEdge
import Cvs.Upstream.SturmLiouvillePrufer

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The rate window near the edge

With the sharp rate bound of Cvs.Prolate.LiouvilleGreen.RateNearEdge, the Prüfer rate of a prolate rung is the frequency `a/p` within the relative
error `ξ/a ≤ ξ/√((ξ² − 1)(c² − χ))`, and the absolute correction is at most `ξ/(ξ² − 1)`: the phase runs at its
frequency to within a few percent as soon as `σs ≳ 5`, where `σ² = (c² − χ)/c²` and `s = c√(2(ξ − 1))`, the
matching point measured for Liouville–Green validity.
-/

namespace Cvs.Prolate.LiouvilleGreen.RateWindowNearEdge

open Real Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Upstream.SturmLiouvillePrufer Cvs.Prolate.LiouvilleGreen.PruferRateFrequency Cvs.Prolate.LiouvilleGreen.RateNearEdge

/-- **The correction near the edge**: `|w|(a/p)/2 ≤ ξ/(ξ² − 1)`. -/
theorem correction_le_edge {c χ ξ : ℝ} (hξ : 1 < ξ) (hc2 : 0 < c ^ 2) (hχc : χ < c ^ 2) :
    |wP c χ ξ| * (aP c χ ξ / pP ξ) / 2 ≤ ξ / (ξ ^ 2 - 1) := by
  have ha := aP_pos hξ hc2 hχc
  have hp := pP_pos hξ
  have hw := wP_pos hξ hc2 hχc
  rw [abs_of_pos hw]
  calc wP c χ ξ * (aP c χ ξ / pP ξ) / 2 ≤ 2 * ξ / aP c χ ξ * (aP c χ ξ / pP ξ) / 2 := by
        have := wP_le_two_div_a hξ hc2 hχc
        gcongr
    _ = ξ / (ξ ^ 2 - 1) := by
        have : pP ξ = ξ ^ 2 - 1 := rfl
        rw [this]; field_simp

/-- **The rate window near the edge**: `(a/p)(1 − ξ/a) ≤ Θ' ≤ (a/p)(1 + ξ/a)` whenever the energy is positive. -/
theorem rate_bounds_edge {c χ ξ : ℝ} {ψ u : ℝ → ℝ} (hξ : 1 < ξ) (hc2 : 0 < c ^ 2) (hχc : χ < c ^ 2)
    (hE : 0 < energy (aP c χ) ψ u ξ) :
    aP c χ ξ / pP ξ * (1 - ξ / aP c χ ξ) ≤ rate pP (aP c χ) (wP c χ) (qP c χ) ψ u ξ
      ∧ rate pP (aP c χ) (wP c χ) (qP c χ) ψ u ξ ≤ aP c χ ξ / pP ξ * (1 + ξ / aP c χ ξ) := by
  have ha := aP_pos hξ hc2 hχc
  have hp := pP_pos hξ
  have hw := wP_pos hξ hc2 hχc
  have hkey := abs_rate_sub_le (p := pP) (a := aP c χ) (w := wP c χ) (q := qP c χ) (ψ := ψ) (u := u)
    ha hp (aP_sq hξ hc2 hχc) hE
  rw [abs_of_pos hw] at hkey
  have hcorr : wP c χ ξ * (aP c χ ξ / pP ξ) / 2 ≤ aP c χ ξ / pP ξ * (ξ / aP c χ ξ) := by
    have := wP_le_two_div_a hξ hc2 hχc
    calc wP c χ ξ * (aP c χ ξ / pP ξ) / 2 ≤ 2 * ξ / aP c χ ξ * (aP c χ ξ / pP ξ) / 2 := by gcongr
      _ = aP c χ ξ / pP ξ * (ξ / aP c χ ξ) := by ring
  have := abs_le.mp hkey
  constructor <;> nlinarith [this.1, this.2, hcorr]

end Cvs.Prolate.LiouvilleGreen.RateWindowNearEdge

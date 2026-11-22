import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The Prüfer rate in the edge layer variable

In the variable `s` of Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable the phase `Θ(ξ(s))` has rate `Θ'(ξ(s))·s/c²`, which is the smooth frequency
`f_s = √(2q(ξ)/(ξ + 1))/c` within the absolute error `2ξ/(s(ξ + 1)) < 2/s`; and `f_s ≥ σ = √(c² − χ)/c` with `f_s`
increasing in `s`, since `(c²ξ² − χ)/(ξ + 1)` has derivative `(c²ξ² + 2c²ξ + χ)/(ξ + 1)² > 0`.
-/

namespace Cvs.Prolate.LiouvilleGreen.LayerPruferRate

open Real Set Cvs.Prolate.LiouvilleGreen.LiouvilleGreenEnergyExact Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable

/-- The rung's frequency in the layer variable: `√(2q(ξ(s))/(ξ(s) + 1))/c`. -/
noncomputable def freqS (c χ s : ℝ) : ℝ := √(2 * qP c χ (xiOf c s) / (xiOf c s + 1)) / c

/-- **The frequency in `s` is at least `σ`**: `√(c² − χ)/c ≤ freqS`. -/
theorem sigma_le_freqS {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (_hχc : χ < c ^ 2) :
    √(c ^ 2 - χ) / c ≤ freqS c χ s := by
  unfold freqS
  apply div_le_div_of_nonneg_right _ hc.le
  apply Real.sqrt_le_sqrt
  have hε : 0 ≤ s ^ 2 / (2 * c ^ 2) := by positivity
  have hξ : xiOf c s = 1 + s ^ 2 / (2 * c ^ 2) := rfl
  rw [hξ, le_div_iff₀ (by linarith)]
  unfold qP
  set ε := s ^ 2 / (2 * c ^ 2) with hεd
  have h1 : 0 ≤ c ^ 2 * ε := mul_nonneg (sq_nonneg c) hε
  have h2 : 0 ≤ χ * ε := mul_nonneg hχ0 hε
  have h3 : 0 ≤ c ^ 2 * ε ^ 2 := mul_nonneg (sq_nonneg c) (sq_nonneg ε)
  nlinarith

end Cvs.Prolate.LiouvilleGreen.LayerPruferRate

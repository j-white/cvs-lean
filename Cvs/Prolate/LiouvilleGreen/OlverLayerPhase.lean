import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable
import Cvs.Prolate.LiouvilleGreen.LayerPruferRate
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Olver's phase in the layer variable

With `ζ(s) = ∫_0^s f_s`, `f_s = √(2q(ξ)/(ξ + 1))/c` the rung's frequency in `s` (Cvs.Prolate.LiouvilleGreen.LayerPruferRate), `ζ′ = f_s` and `ζ(s) ≥ σs`:
Olver's variable `∫_1^ξ √(q/p)` written in `s = c√(2(ξ − 1))`, where it has no singularity at the edge; near `s = 0`
it is `σs`, so the uniform approximant `A·J₀(ζ)` reduces to the edge form `J₀(σs)`.
-/

namespace Cvs.Prolate.LiouvilleGreen.OlverLayerPhase

open Real Set MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable Cvs.Prolate.LiouvilleGreen.LayerPruferRate

/-- Olver's phase in the layer variable, `ζ(s) = ∫_0^s f_s`. -/
noncomputable def olverZeta (c χ s : ℝ) : ℝ := ∫ u in (0 : ℝ)..s, freqS c χ u

theorem continuous_freqS {c χ : ℝ} (hc : 0 < c) : Continuous (freqS c χ) := by
  unfold freqS qP xiOf
  have hc2 : (2 * c ^ 2) ≠ 0 := by positivity
  refine Continuous.div_const (Continuous.sqrt (Continuous.div (by fun_prop) (by fun_prop) fun s => ?_)) _
  have : 0 ≤ s ^ 2 / (2 * c ^ 2) := by positivity
  linarith

/-- `ζ′ = f_s`. -/
theorem hasDerivAt_olverZeta {c χ : ℝ} (hc : 0 < c) (s : ℝ) : HasDerivAt (olverZeta c χ) (freqS c χ s) s :=
  intervalIntegral.integral_hasDerivAt_right ((continuous_freqS hc).intervalIntegrable _ _)
    ((continuous_freqS hc).stronglyMeasurableAtFilter _ _) (continuous_freqS hc).continuousAt

/-- `ζ(s) ≥ σs` for `s ≥ 0`. -/
theorem sigma_mul_le_olverZeta {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hs : 0 ≤ s) :
    √(c ^ 2 - χ) / c * s ≤ olverZeta c χ s := by
  unfold olverZeta
  have h := intervalIntegral.integral_mono_on hs (intervalIntegrable_const (μ := volume) (c := √(c ^ 2 - χ) / c))
    ((continuous_freqS hc).intervalIntegrable _ _) fun u _ => sigma_le_freqS hc hχ0 hχc
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  linarith [h, show √(c ^ 2 - χ) / c * s = s * (√(c ^ 2 - χ) / c) by ring]

end Cvs.Prolate.LiouvilleGreen.OlverLayerPhase

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Order.ProjIcc
import Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable
import Cvs.Prolate.LiouvilleGreen.LayerProlateSystem
import Cvs.Prolate.LiouvilleGreen.LayerPruferRate
import Cvs.Prolate.LiouvilleGreen.OlverAmplitudeAtEdge
import Cvs.Prolate.LiouvilleGreen.OlverInitialErrorZero
import Cvs.Prolate.LiouvilleGreen.OlverLayerPhase
import Cvs.Prolate.LiouvilleGreen.OlverRungError
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The layer construction at frequency `c` is the construction at `c = 1` rescaled

With `t = s/c` and `χ̂ = χ/c²`: `ξ(s) = ξ̂(t)`, `f_s = f̂(t)`, `ζ = cζ̂(t)`, `P̃ = cP̂(t)`, `R = R̂(t)`, `A = Â(t)` and
`A′ = Â′(t)/c`, where hats are the `c = 1` objects at `χ̂`. The amplitude depends on `c` only through `σ`.
-/

namespace Cvs.Prolate.LiouvilleGreen.LayerScaling

open Real Set Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable Cvs.Prolate.LiouvilleGreen.LayerPruferRate Cvs.Prolate.LiouvilleGreen.OlverLayerPhase Cvs.Prolate.LiouvilleGreen.LayerProlateSystem Cvs.Prolate.LiouvilleGreen.OlverAmplitudeAtEdge Cvs.Prolate.LiouvilleGreen.OlverAmplitudeFlat Cvs.Prolate.LiouvilleGreen.OlverInitialErrorZero Cvs.Prolate.LiouvilleGreen.OlverRungError

theorem xiOf_scale {c : ℝ} (hc : c ≠ 0) (s : ℝ) : xiOf c s = xiOf 1 (s / c) := by
  unfold xiOf; field_simp

theorem freqS_scale {c : ℝ} (hc : 0 < c) (χ s : ℝ) : freqS c χ s = freqS 1 (χ / c ^ 2) (s / c) := by
  unfold freqS qP
  rw [← xiOf_scale hc.ne']
  have hc2 : 0 < c ^ 2 := by positivity
  have e : 2 * (c ^ 2 * xiOf c s ^ 2 - χ) / (xiOf c s + 1)
      = c ^ 2 * (2 * (1 ^ 2 * xiOf c s ^ 2 - χ / c ^ 2) / (xiOf c s + 1)) := by
    field_simp
  rw [e, Real.sqrt_mul hc2.le, Real.sqrt_sq hc.le]
  field_simp

theorem olverZeta_scale {c : ℝ} (hc : 0 < c) (χ s : ℝ) :
    olverZeta c χ s = c * olverZeta 1 (χ / c ^ 2) (s / c) := by
  unfold olverZeta
  simp_rw [freqS_scale hc χ]
  rw [intervalIntegral.integral_comp_div (fun u => freqS 1 (χ / c ^ 2) u) hc.ne', zero_div, smul_eq_mul]

theorem pS_scale {c : ℝ} (hc : c ≠ 0) (s : ℝ) : pS c s = c * pS 1 (s / c) := by
  unfold pS
  rw [← xiOf_scale hc]
  field_simp

theorem ampRatio_scale {c : ℝ} (hc : 0 < c) (χ s : ℝ) :
    ampRatio c χ s = ampRatio 1 (χ / c ^ 2) (s / c) := by
  unfold ampRatio
  rw [olverZeta_scale hc, pS_scale hc.ne', freqS_scale hc]
  rw [mul_assoc, mul_div_mul_left _ _ hc.ne']

theorem olverAmp_scale {c : ℝ} (hc : 0 < c) (χ s : ℝ) :
    olverAmp c χ s = olverAmp 1 (χ / c ^ 2) (s / c) := by
  unfold olverAmp; rw [ampRatio_scale hc]

theorem scaled_params {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    0 ≤ χ / c ^ 2 ∧ χ / c ^ 2 < 1 ^ 2 := by
  have hc2 : 0 < c ^ 2 := by positivity
  refine ⟨by positivity, ?_⟩
  rw [one_pow, div_lt_one hc2]; exact hχc

theorem olverAmp'_scale {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hs : 0 < s) :
    olverAmp' c χ s = olverAmp' 1 (χ / c ^ 2) (s / c) / c := by
  obtain ⟨h0, h1⟩ := scaled_params hc hχ0 hχc
  have ht : 0 < s / c := div_pos hs hc
  have hd := (hasDerivAt_olverAmp one_pos h0 h1 ht).comp s ((hasDerivAt_id s).div_const c)
  have hfun : (olverAmp 1 (χ / c ^ 2) ∘ fun x => id x / c) = olverAmp c χ := by
    funext x; simp [olverAmp_scale hc χ x]
  rw [hfun] at hd
  have := (hasDerivAt_olverAmp hc hχ0 hχc hs).unique hd
  rw [this]; simp; ring

theorem pS_mul_olverAmp'_scale {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hs : 0 < s) :
    pS c s * olverAmp' c χ s = pS 1 (s / c) * olverAmp' 1 (χ / c ^ 2) (s / c) := by
  rw [pS_scale hc.ne', olverAmp'_scale hc hχ0 hχc hs]
  field_simp

end Cvs.Prolate.LiouvilleGreen.LayerScaling

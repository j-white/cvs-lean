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
import Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge
import Cvs.Prolate.LiouvilleGreen.LayerFrequencySecondDerivative
import Cvs.Prolate.LiouvilleGreen.LayerProlateSystem
import Cvs.Prolate.LiouvilleGreen.LayerPruferRate
import Cvs.Prolate.LiouvilleGreen.OlverAmplitudeAtEdge
import Cvs.Prolate.LiouvilleGreen.OlverAmplitudeFlat
import Cvs.Prolate.LiouvilleGreen.OlverApproximantSystem
import Cvs.Prolate.LiouvilleGreen.OlverInitialErrorZero
import Cvs.Prolate.LiouvilleGreen.OlverLayerPhase
import Cvs.Prolate.LiouvilleGreen.OlverResidualClosedForm
import Cvs.Prolate.LiouvilleGreen.OlverRungError
import Cvs.Prolate.LiouvilleGreen.OlverTruncatedResidual
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Upstream.BesselJZeroIntegral
import Cvs.Upstream.ForcedOscillatorError

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The two-stage error bound for a prolate rung

On `[s_m, s₁]`, `s_m > 0`, the layer error `e = ψ(ξ(s)) − c₀A J₀(ζ)` with flux `u = u(ξ(s)) − c₀g_p` solves
`e′ = u/P̃`, `u′ = −Q̃e + F` with `F = −c₀wJ₀(ζ)`, and `a = P̃f_s` has `a′/Q̃ = L`. So Cvs.Upstream.ForcedOscillatorError applies with `k = L`: if
`|L| < 2` there and `√Z(s_m) ≤ ε_m` (an earlier result), `|e(s₁)|` is at most `e^{∫β}(√((1 + |L(s_m)|/2)a(s_m))ε_m + ∫γe^{−∫β})`
over `√(d(s₁)a(s₁))`, with `β = |L′|/(4d)`, `γ = |c₀wJ₀(ζ)|(|L| + 2)/(2√(da))`, `d = 1 − |L|/2`.
-/

namespace Cvs.Prolate.LiouvilleGreen.OlverTwoStageError

open Real Set Filter Topology MeasureTheory intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable Cvs.Prolate.LiouvilleGreen.LayerPruferRate Cvs.Upstream.BesselJZeroIntegral Cvs.Prolate.LiouvilleGreen.OlverLayerPhase Cvs.Prolate.LiouvilleGreen.OlverApproximantSystem Cvs.Prolate.LiouvilleGreen.LayerProlateSystem Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge Cvs.Prolate.LiouvilleGreen.OlverAmplitudeAtEdge Cvs.Prolate.LiouvilleGreen.OlverAmplitudeFlat Cvs.Prolate.LiouvilleGreen.OlverInitialErrorZero Cvs.Prolate.LiouvilleGreen.OlverRungError Cvs.Prolate.LiouvilleGreen.LayerFrequencySecondDerivative Cvs.Prolate.LiouvilleGreen.OlverResidualClosedForm Cvs.Prolate.LiouvilleGreen.OlverTruncatedResidual Cvs.Upstream.ForcedOscillatorError

/-- `L = a′/Q̃` for `a = P̃f_s`. -/
theorem logRate_eq {c χ s : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (hs : 0 < s) :
    logRate c χ s = (pS' c s * freqS c χ s + pS c s * freqS' c χ s) / qS c χ s := by
  have hf := freqS_pos (s := s) hc hχc
  have hp := pS_pos hc hs
  rw [← pS_mul_freqS_sq hc hs hχc]
  unfold logRate
  field_simp

theorem continuousAt_logRate' {c χ s : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (hs : 0 < s) :
    ContinuousAt (logRate' c χ) s := by
  have hf := freqS_pos (s := s) hc hχc
  have hp := pS_pos hc hs
  have cf : ContinuousAt (freqS c χ) s := (hasDerivAt_freqS hc hχc s).continuousAt
  have cf' : ContinuousAt (freqS' c χ) s := (hasDerivAt_freqS' hc hχc s).continuousAt
  have cp : ContinuousAt (pS c) s := (hasDerivAt_pS hc s).continuousAt
  have cp' : ContinuousAt (pS' c) s := (hasDerivAt_pS' hc s).continuousAt
  have cf'' : ContinuousAt (freqS'' c χ) s := by
    unfold freqS''
    have hξ1 : 0 < xiOf c s + 1 := by linarith [one_le_xiOf c s]
    have cx : ContinuousAt (xiOf c) s := (hasDerivAt_xiOf c s hc.ne').continuousAt
    have crx : ContinuousAt (fun y => radXi c χ (xiOf c y)) s :=
      ((hasDerivAt_radXi (c := c) (χ := χ) hξ1.ne').continuousAt).comp cx
    refine ContinuousAt.sub (ContinuousAt.div (crx.add ((continuousAt_id.pow 2 |>.div_const _).mul
      (continuousAt_const.div ((cx.add continuousAt_const).pow 3) (pow_pos hξ1 3).ne'))) (continuousAt_const.mul cf)
      (mul_pos (by positivity : (0:ℝ) < 2 * c ^ 4) hf).ne') (ContinuousAt.div ((continuousAt_id.mul crx).mul cf')
      (continuousAt_const.mul (cf.pow 2)) (mul_pos (by positivity : (0:ℝ) < 2 * c ^ 4) (pow_pos hf 2)).ne')
  unfold logRate'
  have hpf : pS c s * freqS c χ s ≠ 0 := (mul_pos hp hf).ne'
  exact ((((continuousAt_const.mul continuousAt_id).div_const _).div (cp.mul cf) hpf).sub
    ((cp'.mul ((cp'.mul cf).add (cp.mul cf'))).div ((cp.mul cf).pow 2) (pow_ne_zero 2 hpf))).add
    (cf''.div (cf.pow 2) (pow_pos hf 2).ne') |>.sub ((continuousAt_const.mul (cf'.pow 2)).div (cf.pow 3)
    (pow_pos hf 3).ne')

/-- **The two-stage error bound for a prolate rung.** -/
theorem abs_rung_sub_approx_le_two_stage {ψ u : ℝ → ℝ} {c χ c₀ sm s₁ εm : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ)
    (hχc : χ < c ^ 2) (hsm : 0 < sm) (hs : sm ≤ s₁)
    (hψ : ∀ s ∈ Icc sm s₁, HasDerivAt ψ (u (xiOf c s) / pP (xiOf c s)) (xiOf c s))
    (hu : ∀ s ∈ Icc sm s₁, HasDerivAt u (-(qP c χ (xiOf c s) * ψ (xiOf c s))) (xiOf c s))
    (hk2 : ∀ s ∈ Icc sm s₁, |logRate c χ s| < 2)
    (hZ : √((ψ (xiOf c sm) - c₀ * approx c χ sm) ^ 2
        + (u (xiOf c sm) - c₀ * approxFlux c χ sm) ^ 2 / (pS c sm * freqS c χ sm) ^ 2) ≤ εm) :
    |ψ (xiOf c s₁) - c₀ * approx c χ s₁|
      ≤ exp (∫ t in sm..s₁, |logRate' c χ t| / (4 * (1 - |logRate c χ t| / 2)))
        * (√((1 + |logRate c χ sm| / 2) * (pS c sm * freqS c χ sm)) * εm
          + ∫ x in sm..s₁, |-(c₀ * (olverResid c χ x * besselJ0 (olverZeta c χ x)))|
              * (|logRate c χ x| + 2) / (2 * √((1 - |logRate c χ x| / 2) * (pS c x * freqS c χ x)))
            * exp (-∫ t in sm..x, |logRate' c χ t| / (4 * (1 - |logRate c χ t| / 2))))
        / √((1 - |logRate c χ s₁| / 2) * (pS c s₁ * freqS c χ s₁)) := by
  have hpos : ∀ s ∈ Icc sm s₁, 0 < s := fun s hs' => lt_of_lt_of_le hsm hs'.1
  set a : ℝ → ℝ := fun s => pS c s * freqS c χ s with had
  set F : ℝ → ℝ := fun s => -(c₀ * (olverResid c χ s * besselJ0 (olverZeta c χ s))) with hFd
  have ha0 : ∀ s ∈ Icc sm s₁, 0 < a s := fun s hs' => mul_pos (pS_pos hc (hpos s hs')) (freqS_pos hc hχc)
  -- the error system on `[s_m, s₁]`
  have hg : ∀ s ∈ Icc sm s₁, HasDerivAt (approx c χ) (approxFlux c χ s / pS c s) s := fun s hs' =>
    hasDerivAt_approx (hasDerivAt_olverAmp hc hχ0 hχc (hpos s hs')) (hasDerivAt_olverZeta hc s)
      (pS_pos hc (hpos s hs')).ne'
  have hgp : ∀ s ∈ Icc sm s₁, HasDerivAt (approxFlux c χ)
      (olverResid c χ s * besselJ0 (olverZeta c χ s) - qS c χ s * approx c χ s) s := fun s hs' => by
    have hs'' := hpos s hs'
    have hW := (hasDerivAt_pS hc s).mul (hasDerivAt_freqS hc hχc s)
    have hR := ampRatio_pos hc hχ0 hχc hs''
    have hσ : 0 < √(c ^ 2 - χ) / c := div_pos (Real.sqrt_pos.mpr (by linarith)) hc
    refine hasDerivAt_flux (W := fun y => pS c y * freqS c χ y) (hasDerivAt_olverAmp hc hχ0 hχc hs'')
      (hasDerivAt_olverZeta hc s) hW (hasDerivAt_pS_mul_olverAmp' hc hχ0 hχc hs'') ?_
      (Eventually.of_forall fun y => rfl) (pS_mul_freqS_sq hc hs'' hχc) (Real.sqrt_pos.mpr hR).ne'
      (lt_of_lt_of_le (mul_pos hσ hs'') (sigma_mul_le_olverZeta hc hχ0 hχc hs''.le)).ne'
    filter_upwards [Ioi_mem_nhds hs''] with y hy
    have hy' : 0 < y := hy
    unfold olverAmp
    rw [Real.sq_sqrt (ampRatio_pos hc hχ0 hχc hy').le]
    unfold ampRatio
    have h1 := (pS_pos hc hy').ne'
    have h2 := (freqS_pos (s := y) hc hχc).ne'
    field_simp
  have he : ∀ s ∈ Icc sm s₁, HasDerivAt (fun s => ψ (xiOf c s) - c₀ * approx c χ s)
      ((u (xiOf c s) - c₀ * approxFlux c χ s) / pS c s) s := fun s hs' => by
    have := (hasDerivAt_layer_psi hc (hpos s hs') (hψ s hs')).sub ((hg s hs').const_mul c₀)
    refine this.congr_deriv ?_
    have := (pS_pos hc (hpos s hs')).ne'
    field_simp
  have hu' : ∀ s ∈ Icc sm s₁, HasDerivAt (fun s => u (xiOf c s) - c₀ * approxFlux c χ s)
      (-(qS c χ s * (ψ (xiOf c s) - c₀ * approx c χ s)) + F s) s := fun s hs' => by
    have := (hasDerivAt_layer_u hc (hu s hs')).sub ((hgp s hs').const_mul c₀)
    refine this.congr_deriv ?_
    simp only [hFd]; ring
  have hmain := abs_le_liouville hs he hu'
    (a := a) (a' := fun s => pS' c s * freqS c χ s + pS c s * freqS' c χ s)
    (fun s hs' => (hasDerivAt_pS hc s).mul (hasDerivAt_freqS hc hχc s))
    (fun s hs' => hasDerivAt_logRate hc hχc (hpos s hs')) ha0 (fun s hs' => (pS_pos hc (hpos s hs')).ne')
    (fun s hs' => by
      simp only [had]
      rw [← pS_mul_freqS_sq hc (hpos s hs') hχc]; ring)
    (fun s hs' => logRate_eq hc hχc (hpos s hs')) hk2
    (fun s hs' => by
      have hs'' := hpos s hs'
      have hd : 0 < 1 - |logRate c χ s| / 2 := by linarith [hk2 s hs']
      exact (((continuous_abs.continuousAt.comp (continuousAt_logRate' hc hχc hs'')).div
        (continuousAt_const.mul (continuousAt_const.sub ((continuous_abs.continuousAt.comp
          (hasDerivAt_logRate hc hχc hs'').continuousAt).div_const 2))) (mul_pos (by norm_num) hd).ne')).continuousWithinAt)
    (fun s hs' => by
      have hs'' := hpos s hs'
      have hd : 0 < 1 - |logRate c χ s| / 2 := by linarith [hk2 s hs']
      have cL : ContinuousAt (logRate c χ) s := (hasDerivAt_logRate hc hχc hs'').continuousAt
      have ca : ContinuousAt a s :=
        ((hasDerivAt_pS hc s).mul (hasDerivAt_freqS hc hχc s)).continuousAt
      have cF : ContinuousAt F s := by
        refine ((continuousAt_const.mul ((continuousAt_olverResid hc hχ0 hχc hs'').mul ?_))).neg
        exact continuous_besselJ0.continuousAt.comp (hasDerivAt_olverZeta (χ := χ) hc s).continuousAt
      have hdA : 0 < (1 - |logRate c χ s| / 2) * a s := mul_pos hd (ha0 s hs')
      exact (((continuous_abs.continuousAt.comp cF).mul
        ((continuous_abs.continuousAt.comp cL).add continuousAt_const)).div
        (continuousAt_const.mul ((continuousAt_const.sub ((continuous_abs.continuousAt.comp cL).div_const 2)).mul
          ca).sqrt) (mul_pos two_pos (Real.sqrt_pos.mpr hdA)).ne').continuousWithinAt)
  refine hmain.trans (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  refine mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) (exp_pos _).le
  -- the initial Liouville energy from `√Z(s_m)`
  have hsm' : sm ∈ Icc sm s₁ := ⟨le_rfl, hs⟩
  have ha' := ha0 sm hsm'
  have hE : a sm * (ψ (xiOf c sm) - c₀ * approx c χ sm) ^ 2
      + (u (xiOf c sm) - c₀ * approxFlux c χ sm) ^ 2 / a sm
      = a sm * ((ψ (xiOf c sm) - c₀ * approx c χ sm) ^ 2
        + (u (xiOf c sm) - c₀ * approxFlux c χ sm) ^ 2 / (pS c sm * freqS c χ sm) ^ 2) := by
    have h1 := (pS_pos hc hsm).ne'
    have h2 := (freqS_pos (s := sm) hc hχc).ne'
    simp only [had]; field_simp
  rw [hE, ← mul_assoc, Real.sqrt_mul (by positivity)]
  exact mul_le_mul_of_nonneg_left hZ (Real.sqrt_nonneg _)

end Cvs.Prolate.LiouvilleGreen.OlverTwoStageError

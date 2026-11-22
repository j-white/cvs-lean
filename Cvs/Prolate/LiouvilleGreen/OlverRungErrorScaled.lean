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
import Cvs.Prolate.LiouvilleGreen.LayerProlateSystem
import Cvs.Prolate.LiouvilleGreen.LayerPruferRate
import Cvs.Prolate.LiouvilleGreen.LayerScaling
import Cvs.Prolate.LiouvilleGreen.OlverInitialErrorZero
import Cvs.Prolate.LiouvilleGreen.OlverLayerPhase
import Cvs.Prolate.LiouvilleGreen.OlverRungError
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Upstream.BesselJZeroIntegral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Olver's error for a prolate rung is `O(1/c)` with a `c`-free constant

If `ŵ = (P̂Â′)′` is the residual of the `c = 1` construction at `χ̂ = χ/c²`, continuous on `(0, t₁]` with
`|ŵ|/(P̂f̂)` integrable on `[0, t₁]`, `t₁ = s₁/c`, then the residual at frequency `c` is `w(s) = ŵ(s/c)/c` and Cvs.Prolate.LiouvilleGreen.OlverRungError
gives `|ψ(ξ(s₁)) − c₀A(s₁)J₀(ζ(s₁))| ≤ (|c₀|/c)·∫_0^{t₁} |ŵ|/(P̂f̂)`, using `|J₀| ≤ 1`.
-/

namespace Cvs.Prolate.LiouvilleGreen.OlverRungErrorScaled

open Real Set Filter Topology MeasureTheory Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable Cvs.Prolate.LiouvilleGreen.LayerPruferRate Cvs.Upstream.BesselJZeroIntegral Cvs.Prolate.LiouvilleGreen.OlverLayerPhase Cvs.Prolate.LiouvilleGreen.LayerProlateSystem Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge Cvs.Prolate.LiouvilleGreen.OlverAmplitudeFlat Cvs.Prolate.LiouvilleGreen.OlverInitialErrorZero Cvs.Prolate.LiouvilleGreen.OlverRungError Cvs.Prolate.LiouvilleGreen.LayerScaling

/-- **Olver's error for a prolate rung, with the `c`-free residual constant.** -/
theorem abs_rung_sub_approx_le_scaled {ψ u ŵ : ℝ → ℝ} {c χ c₀ C s₁ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ)
    (hχc : χ < c ^ 2) (hs₁ : 0 < s₁)
    (hψ : ∀ ξ ∈ Ioc 1 (xiOf c s₁), HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 (xiOf c s₁), HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hedge : Tendsto (fun s => ψ (xiOf c s)) (𝓝[>] 0) (𝓝 c₀))
    (hflux : ∀ᶠ s in 𝓝[>] 0, |u (xiOf c s)| ≤ C * s ^ 2)
    (hŵ : ∀ t ∈ Ioc 0 (s₁ / c), HasDerivAt (fun y => pS 1 y * olverAmp' 1 (χ / c ^ 2) y) (ŵ t) t)
    (hŵc : ContinuousOn ŵ (Ioc 0 (s₁ / c)))
    (hK : IntervalIntegrable (fun t => |ŵ t| / (pS 1 t * freqS 1 (χ / c ^ 2) t)) volume 0 (s₁ / c)) :
    |ψ (xiOf c s₁) - c₀ * approx c χ s₁|
      ≤ |c₀| / c * ∫ t in (0 : ℝ)..s₁ / c, |ŵ t| / (pS 1 t * freqS 1 (χ / c ^ 2) t) := by
  set χh := χ / c ^ 2
  set h : ℝ → ℝ := fun t => |ŵ t| / (pS 1 t * freqS 1 χh t) with hhd
  set w : ℝ → ℝ := fun s => ŵ (s / c) / c with hwd
  have hsc : ∀ s ∈ Ioc 0 s₁, s / c ∈ Ioc 0 (s₁ / c) := fun s hs =>
    ⟨div_pos hs.1 hc, div_le_div_of_nonneg_right hs.2 hc.le⟩
  -- the residual at frequency `c`
  have hw : ∀ s ∈ Ioc 0 s₁, HasDerivAt (fun y => pS c y * olverAmp' c χ y) (w s) s := fun s hs => by
    have hd := (hŵ (s / c) (hsc s hs)).comp s ((hasDerivAt_id s).div_const c)
    have hfun : ∀ᶠ y in 𝓝 s, pS c y * olverAmp' c χ y
        = ((fun y => pS 1 y * olverAmp' 1 χh y) ∘ fun x => id x / c) y := by
      filter_upwards [Ioi_mem_nhds hs.1] with y hy
      simp only [Function.comp, id]
      exact pS_mul_olverAmp'_scale hc hχ0 hχc hy
    refine (hd.congr_of_eventuallyEq hfun).congr_deriv ?_
    simp [hwd]; ring
  have hwc : ContinuousOn w (Ioc 0 s₁) :=
    (hŵc.comp (continuous_id.div_const c).continuousOn fun s hs => hsc s hs).div_const c
  -- the integrand at `c` against the rescaled `c`-free one
  set F : ℝ → ℝ := fun s => |c₀ * (w s * besselJ0 (olverZeta c χ s))| / (pS c s * freqS c χ s) with hFd
  have hFle : ∀ s ∈ Icc 0 s₁, F s ≤ |c₀| / c ^ 2 * h (s / c) := fun s hs => by
    rcases eq_or_lt_of_le hs.1 with h0 | hpos
    · subst h0; simp [hFd, hhd, pS]
    have hp := pS_pos hc hpos
    have hf := freqS_pos (s := s) hc hχc
    have hJ := abs_besselJ0_le (olverZeta c χ s)
    simp only [hFd, hhd, hwd]
    rw [pS_scale hc.ne', freqS_scale hc] at *
    have hp1 : 0 < pS 1 (s / c) := by
      have := pS_pos hc hpos; rw [pS_scale hc.ne'] at this; exact pos_of_mul_pos_right this hc.le
    have hf1 : 0 < freqS 1 χh (s / c) := by rw [← freqS_scale hc]; exact freqS_pos hc hχc
    rw [abs_mul, abs_mul, abs_div, abs_of_pos hc]
    rw [div_le_iff₀ (by positivity)]
    have hx : 0 ≤ |c₀| * (|ŵ (s / c)| / c) := by positivity
    calc |c₀| * (|ŵ (s / c)| / c * |besselJ0 (olverZeta c χ s)|) ≤ |c₀| * (|ŵ (s / c)| / c * 1) := by
          gcongr
      _ = |c₀| / c ^ 2 * (|ŵ (s / c)| / (pS 1 (s / c) * freqS 1 χh (s / c))) * (c * pS 1 (s / c) * freqS 1 χh (s / c)) := by
          field_simp
  -- integrability
  have hKc : IntervalIntegrable (fun s => |c₀| / c ^ 2 * h (s / c)) volume 0 s₁ := by
    have h1 := hK.comp_mul_right (c := c⁻¹)
    have e1 : (0 : ℝ) / c⁻¹ = 0 := by simp
    have e2 : s₁ / c / c⁻¹ = s₁ := by field_simp
    rw [e1, e2] at h1
    have h2 := h1.const_mul (|c₀| / c ^ 2)
    refine h2.congr ?_
    exact fun x _ => by simp only [div_eq_mul_inv]
  have hFm : AEStronglyMeasurable F (volume.restrict (Ioc 0 s₁)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine ContinuousOn.div ?_ ?_ fun s hs => (mul_pos (pS_pos hc hs.1) (freqS_pos hc hχc)).ne'
    · refine continuous_abs.comp_continuousOn (continuousOn_const.mul (hwc.mul ?_))
      exact (continuous_besselJ0.comp (continuous_iff_continuousAt.2 fun x =>
        (hasDerivAt_olverZeta (χ := χ) hc x).continuousAt)).continuousOn
    · exact ((continuous_pS c).mul (continuous_freqS hc)).continuousOn
  have hint : IntervalIntegrable F volume 0 s₁ := by
    refine hKc.mono_fun ?_ ?_
    · rw [uIoc_of_le hs₁.le]; exact hFm
    · rw [uIoc_of_le hs₁.le]
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs => ?_)
      simp only [Real.norm_eq_abs]
      rw [abs_of_nonneg (div_nonneg (abs_nonneg _)
        (mul_pos (pS_pos hc hs.1) (freqS_pos hc hχc)).le)]
      exact (hFle s ⟨hs.1.le, hs.2⟩).trans (le_abs_self _)
  have hmain := abs_rung_sub_approx_le hc hχ0 hχc hs₁ hψ hu hedge hflux hw hwc hint
  refine hmain.trans ?_
  calc ∫ s in (0 : ℝ)..s₁, F s ≤ ∫ s in (0 : ℝ)..s₁, |c₀| / c ^ 2 * h (s / c) :=
        intervalIntegral.integral_mono_on hs₁.le hint hKc hFle
    _ = |c₀| / c * ∫ t in (0 : ℝ)..s₁ / c, h t := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div h hc.ne', zero_div,
          smul_eq_mul]
        field_simp

end Cvs.Prolate.LiouvilleGreen.OlverRungErrorScaled

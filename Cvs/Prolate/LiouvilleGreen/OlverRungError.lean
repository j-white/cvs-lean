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
import Cvs.Prolate.LiouvilleGreen.ApproximantErrorContinuous
import Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable
import Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge
import Cvs.Prolate.LiouvilleGreen.LayerProlateSystem
import Cvs.Prolate.LiouvilleGreen.LayerPruferRate
import Cvs.Prolate.LiouvilleGreen.OlverAmplitudeAtEdge
import Cvs.Prolate.LiouvilleGreen.OlverAmplitudeFlat
import Cvs.Prolate.LiouvilleGreen.OlverApproximantSystem
import Cvs.Prolate.LiouvilleGreen.OlverInitialErrorZero
import Cvs.Prolate.LiouvilleGreen.OlverLayerPhase
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
# Olver's error bound for a prolate rung

For a rung `ψ′ = u/p`, `u′ = −qψ` on `(1, ξ(s₁)]` with `ψ(ξ(s)) → c₀` and `|u(ξ(s))| ≤ Cs²` at the edge, and
`w = (P̃A′)′` continuous on `(0, s₁]` with `|c₀wJ₀(ζ)|/a` integrable on `[0, s₁]`:
`|ψ(ξ(s₁)) − c₀A(s₁)J₀(ζ(s₁))| ≤ ∫_0^{s₁} |c₀wJ₀(ζ)|/a`, `a = P̃f_s` — Cvs.Prolate.LiouvilleGreen.ApproximantErrorContinuous on `[s₀, s₁]` and Cvs.Prolate.LiouvilleGreen.OlverInitialErrorZero as `s₀ → 0`.
-/

namespace Cvs.Prolate.LiouvilleGreen.OlverRungError

open Real Set Filter Topology MeasureTheory Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable Cvs.Prolate.LiouvilleGreen.LayerPruferRate Cvs.Upstream.BesselJZeroIntegral Cvs.Upstream.BesselJZeroEquation Cvs.Prolate.LiouvilleGreen.OlverLayerPhase Cvs.Prolate.LiouvilleGreen.OlverApproximantSystem Cvs.Prolate.LiouvilleGreen.LayerProlateSystem Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge Cvs.Prolate.LiouvilleGreen.OlverPhaseBracket Cvs.Prolate.LiouvilleGreen.OlverAmplitudeAtEdge Cvs.Prolate.LiouvilleGreen.OlverAmplitudeFlat Cvs.Prolate.LiouvilleGreen.OlverInitialErrorZero Cvs.Prolate.LiouvilleGreen.ApproximantErrorContinuous

theorem continuous_pS (c : ℝ) : Continuous (pS c) := by
  unfold pS xiOf; fun_prop

theorem ampRatio_pos {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hs : 0 < s) :
    0 < ampRatio c χ s := by
  have hσ : 0 < √(c ^ 2 - χ) / c := div_pos (Real.sqrt_pos.mpr (by linarith)) hc
  have hζ := sigma_mul_le_olverZeta hc hχ0 hχc hs.le
  unfold ampRatio
  exact div_pos (lt_of_lt_of_le (mul_pos hσ hs) hζ) (mul_pos (pS_pos hc hs) (freqS_pos hc hχc))

theorem hasDerivAt_olverAmp {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hs : 0 < s) :
    HasDerivAt (olverAmp c χ) (olverAmp' c χ s) s :=
  (hasDerivAt_ampRatio hc hχc hs).sqrt (ampRatio_pos hc hχ0 hχc hs).ne'

/-- **Olver's error bound for a prolate rung.** -/
theorem abs_rung_sub_approx_le {ψ u w : ℝ → ℝ} {c χ c₀ C s₁ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hs₁ : 0 < s₁)
    (hψ : ∀ ξ ∈ Ioc 1 (xiOf c s₁), HasDerivAt ψ (u ξ / pP ξ) ξ)
    (hu : ∀ ξ ∈ Ioc 1 (xiOf c s₁), HasDerivAt u (-(qP c χ ξ * ψ ξ)) ξ)
    (hedge : Tendsto (fun s => ψ (xiOf c s)) (𝓝[>] 0) (𝓝 c₀))
    (hflux : ∀ᶠ s in 𝓝[>] 0, |u (xiOf c s)| ≤ C * s ^ 2)
    (hw : ∀ s ∈ Ioc 0 s₁, HasDerivAt (fun y => pS c y * olverAmp' c χ y) (w s) s)
    (hwc : ContinuousOn w (Ioc 0 s₁))
    (hint : IntervalIntegrable (fun s => |c₀ * (w s * besselJ0 (olverZeta c χ s))| / (pS c s * freqS c χ s))
      volume 0 s₁) :
    |ψ (xiOf c s₁) - c₀ * approx c χ s₁|
      ≤ ∫ s in (0 : ℝ)..s₁, |c₀ * (w s * besselJ0 (olverZeta c χ s))| / (pS c s * freqS c χ s) := by
  set F : ℝ → ℝ := fun s => |c₀ * (w s * besselJ0 (olverZeta c χ s))| / (pS c s * freqS c χ s) with hFd
  set I := ∫ s in (0 : ℝ)..s₁, F s
  -- the layer lies inside the rung's interval
  have hxi : ∀ s ∈ Ioc 0 s₁, xiOf c s ∈ Ioc 1 (xiOf c s₁) := fun s hs => by
    refine ⟨one_lt_xiOf hc hs.1, ?_⟩
    unfold xiOf
    have : s ^ 2 ≤ s₁ ^ 2 := pow_le_pow_left₀ hs.1.le hs.2 2
    gcongr
  -- the bound on each `[s₀, s₁]`
  have hstep : ∀ s₀ ∈ Ioo 0 s₁, |ψ (xiOf c s₁) - c₀ * approx c χ s₁|
      ≤ √((ψ (xiOf c s₀) - c₀ * approx c χ s₀) ^ 2
        + (u (xiOf c s₀) - c₀ * approxFlux c χ s₀) ^ 2 / (pS c s₀ * freqS c χ s₀) ^ 2) + I := by
    intro s₀ hs₀
    have hpos : ∀ s ∈ Icc s₀ s₁, 0 < s := fun s hs => lt_of_lt_of_le hs₀.1 hs.1
    have hIoc : ∀ s ∈ Icc s₀ s₁, s ∈ Ioc 0 s₁ := fun s hs => ⟨hpos s hs, hs.2⟩
    have hmain := abs_error_le_on (ψ := fun s => ψ (xiOf c s)) (uψ := fun s => u (xiOf c s))
      (g := approx c χ) (gp := approxFlux c χ) (r := fun s => w s * besselJ0 (olverZeta c χ s))
      (a := fun s => pS c s * freqS c χ s)
      (a' := fun s => (1 + 3 * s ^ 2 / (4 * c ^ 2)) * freqS c χ s
        + pS c s * (s * radXi c χ (xiOf c s) / (2 * c ^ 4 * freqS c χ s)))
      (P := pS c) (Q := qS c χ) (c₀ := c₀) hs₀.2.le
      (fun s hs => hasDerivAt_layer_psi hc (hpos s hs) (hψ _ (hxi s (hIoc s hs))))
      (fun s hs => hasDerivAt_layer_u hc (hu _ (hxi s (hIoc s hs))))
      (fun s hs => hasDerivAt_approx (hasDerivAt_olverAmp hc hχ0 hχc (hpos s hs))
        (hasDerivAt_olverZeta hc s) (pS_pos hc (hpos s hs)).ne')
      (fun s hs => by
        have hs' := hpos s hs
        have hW := (hasDerivAt_pS hc s).mul (hasDerivAt_freqS hc hχc s)
        have hR := ampRatio_pos hc hχ0 hχc hs'
        have hWpos : ∀ y, 0 < y → 0 < pS c y * freqS c χ y := fun y hy =>
          mul_pos (pS_pos hc hy) (freqS_pos hc hχc)
        refine hasDerivAt_flux (W := fun y => pS c y * freqS c χ y) (hasDerivAt_olverAmp hc hχ0 hχc hs')
          (hasDerivAt_olverZeta hc s) hW (hw s (hIoc s hs)) ?_ (Eventually.of_forall fun y => rfl)
          (pS_mul_freqS_sq hc hs' hχc) (Real.sqrt_pos.mpr hR).ne' ?_
        · filter_upwards [Ioi_mem_nhds hs'] with y hy
          have hRy := ampRatio_pos hc hχ0 hχc hy
          unfold olverAmp
          rw [Real.sq_sqrt hRy.le]
          unfold ampRatio
          have hy' : 0 < y := hy
          have h1 := (pS_pos hc hy').ne'
          have h2 := (freqS_pos (s := y) hc hχc).ne'
          field_simp
        · have hσ : 0 < √(c ^ 2 - χ) / c := div_pos (Real.sqrt_pos.mpr (by linarith)) hc
          exact (lt_of_lt_of_le (mul_pos hσ hs') (sigma_mul_le_olverZeta hc hχ0 hχc hs'.le)).ne')
      (fun s hs => (hasDerivAt_pS hc s).mul (hasDerivAt_freqS hc hχc s))
      (fun s hs => mul_pos (pS_pos hc (hpos s hs)) (freqS_pos hc hχc))
      (fun s hs => by
        have hs' := hpos s hs
        have hb := (freqS_deriv_bounds hc hχ0 hχc hs'.le).1
        have := freqS_pos (s := s) hc hχc
        have := pS_pos hc hs'
        positivity)
      (fun s hs => (pS_pos hc (hpos s hs)).ne')
      (fun s hs => by
        have := pS_mul_freqS_sq hc (hpos s hs) hχc
        rw [← this]; ring)
      (by
        refine ContinuousOn.div ?_ ?_ fun s hs => (mul_pos (pS_pos hc (hpos s hs)) (freqS_pos hc hχc)).ne'
        · refine (continuous_abs.comp_continuousOn ?_)
          refine continuousOn_const.mul ((hwc.mono fun s hs => hIoc s hs).mul ?_)
          exact (continuous_besselJ0.comp (continuous_iff_continuousAt.2 fun x =>
            (hasDerivAt_olverZeta (χ := χ) hc x).continuousAt)).continuousOn
        · exact ((continuous_pS c).mul (continuous_freqS hc)).continuousOn)
    refine hmain.trans (add_le_add le_rfl ?_)
    exact intervalIntegral.integral_mono_interval hs₀.1.le hs₀.2.le le_rfl
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun s hs =>
        div_nonneg (abs_nonneg _) (mul_pos (pS_pos hc hs.1) (freqS_pos hc hχc)).le)) hint
  -- the edge limit
  have hS := tendsto_edge_energy (ψ := ψ) (u := u) hc hχ0 hχc hedge hflux
  have hS' : Tendsto (fun s₀ => √((ψ (xiOf c s₀) - c₀ * approx c χ s₀) ^ 2
      + (u (xiOf c s₀) - c₀ * approxFlux c χ s₀) ^ 2 / (pS c s₀ * freqS c χ s₀) ^ 2) + I) (𝓝[>] 0) (𝓝 (0 + I)) := by
    refine (hS.congr' ?_).add tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [pS_mul_freqS hc hs hχc]
  rw [zero_add] at hS'
  refine ge_of_tendsto hS' ?_
  filter_upwards [Ioo_mem_nhdsGT hs₁] with s₀ hs₀ using hstep s₀ hs₀

end Cvs.Prolate.LiouvilleGreen.OlverRungError

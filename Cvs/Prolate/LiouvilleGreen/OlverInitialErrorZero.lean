import Mathlib.Analysis.Calculus.Deriv.MeanValue
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
import Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable
import Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge
import Cvs.Prolate.LiouvilleGreen.LayerProlateSystem
import Cvs.Prolate.LiouvilleGreen.LayerPruferRate
import Cvs.Prolate.LiouvilleGreen.OlverAmplitudeAtEdge
import Cvs.Prolate.LiouvilleGreen.OlverAmplitudeFlat
import Cvs.Prolate.LiouvilleGreen.OlverLayerPhase
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval
import Cvs.Upstream.BesselJZeroEquation
import Cvs.Upstream.BesselJZeroIntegral

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The initial error energy vanishes at the edge

For the layer approximant `g = A·J₀(ζ)`, `A = √R`, with flux `g_p = P̃(A′J₀(ζ) + Af_sJ₀′(ζ))`, `A′ = R′/(2A)`:
`g → 1` and `g_p/a → 0` as `s → 0⁺` (Cvs.Prolate.LiouvilleGreen.OlverAmplitudeAtEdge, Cvs.Prolate.LiouvilleGreen.OlverAmplitudeFlat). So for a rung with `ψ(ξ(s)) → c₀` and flux `|u(ξ(s))| ≤ Cs²`,
the initial energy `√((ψ − c₀g)² + (u − c₀g_p)²/a²)` of an earlier result tends to zero at the edge.
-/

namespace Cvs.Prolate.LiouvilleGreen.OlverInitialErrorZero

open Real Set Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable Cvs.Prolate.LiouvilleGreen.LayerPruferRate Cvs.Upstream.BesselJZeroIntegral Cvs.Upstream.BesselJZeroEquation Cvs.Prolate.LiouvilleGreen.OlverLayerPhase Cvs.Prolate.LiouvilleGreen.LayerProlateSystem Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge Cvs.Prolate.LiouvilleGreen.OlverAmplitudeAtEdge Cvs.Prolate.LiouvilleGreen.OlverAmplitudeFlat

/-- Olver's amplitude `A = √R`. -/
noncomputable def olverAmp (c χ s : ℝ) : ℝ := √(ampRatio c χ s)

/-- Its derivative `A′ = R′/(2A)`. -/
noncomputable def olverAmp' (c χ s : ℝ) : ℝ := ampRatio' c χ s / (2 * olverAmp c χ s)

/-- The layer approximant `g = A·J₀(ζ)`. -/
noncomputable def approx (c χ s : ℝ) : ℝ := olverAmp c χ s * besselJ0 (olverZeta c χ s)

/-- Its flux `g_p = P̃(A′J₀(ζ) + Af_sJ₀′(ζ))`. -/
noncomputable def approxFlux (c χ s : ℝ) : ℝ :=
  pS c s * (olverAmp' c χ s * besselJ0 (olverZeta c χ s)
    + olverAmp c χ s * freqS c χ s * besselJ0' (olverZeta c χ s))

theorem besselJ0'_zero : besselJ0' 0 = 0 := by unfold besselJ0'; simp

theorem continuous_besselJ0 : Continuous besselJ0 :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_besselJ0 x).continuousAt

theorem continuous_besselJ0' : Continuous besselJ0' :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_besselJ0' x).continuousAt

theorem tendsto_olverZeta {c χ : ℝ} (hc : 0 < c) : Tendsto (olverZeta c χ) (𝓝[>] 0) (𝓝 0) := by
  have h := (hasDerivAt_olverZeta (χ := χ) hc 0).continuousAt.tendsto
  have h0 : olverZeta c χ 0 = 0 := by simp [olverZeta]
  rw [h0] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_freqS {c χ : ℝ} (hc : 0 < c) : Tendsto (freqS c χ) (𝓝[>] 0) (𝓝 (√(c ^ 2 - χ) / c)) := by
  have h := (continuous_freqS (χ := χ) hc).continuousAt (x := 0) |>.tendsto
  rw [freqS_zero hc] at h
  exact h.mono_left nhdsWithin_le_nhds

theorem tendsto_ampRatio' {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    Tendsto (ampRatio' c χ) (𝓝[>] 0) (𝓝 0) := by
  set K := 1 / c ^ 2 * (1 + 3 / (2 * (√(c ^ 2 - χ) / c) ^ 2))
  have hK : Tendsto (fun s : ℝ => K * s) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun s : ℝ => K * s) (𝓝 0) (𝓝 (K * 0)) := tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hK
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [Real.norm_eq_abs]
  refine (abs_ampRatio'_le hc hχ0 hχc hs).trans (le_of_eq ?_)
  simp only [K]; ring

/-- **`A′ → 0` at the edge.** -/
theorem tendsto_olverAmp' {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    Tendsto (olverAmp' c χ) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun s => ampRatio' c χ s / (2 * olverAmp c χ s)) (𝓝[>] 0) (𝓝 (0 / (2 * 1))) :=
    (tendsto_ampRatio' hc hχ0 hχc).div ((tendsto_olverAmp hc hχ0 hχc).const_mul 2) (by norm_num)
  rw [zero_div] at h
  exact h

/-- **`g → 1` at the edge.** -/
theorem tendsto_approx {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    Tendsto (approx c χ) (𝓝[>] 0) (𝓝 1) := by
  have hJ := (continuous_besselJ0.tendsto 0).comp (tendsto_olverZeta (χ := χ) hc)
  rw [besselJ0_zero] at hJ
  have h : Tendsto (fun s => olverAmp c χ s * besselJ0 (olverZeta c χ s)) (𝓝[>] 0) (𝓝 (1 * 1)) :=
    (tendsto_olverAmp hc hχ0 hχc).mul hJ
  rw [mul_one] at h
  exact h

/-- **`g_p/a → 0` at the edge.** -/
theorem tendsto_approxFlux_div {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    Tendsto (fun s => approxFlux c χ s / aP c χ (xiOf c s)) (𝓝[>] 0) (𝓝 0) := by
  have hσ : 0 < √(c ^ 2 - χ) / c := div_pos (Real.sqrt_pos.mpr (by linarith)) hc
  have hJ := (continuous_besselJ0.tendsto 0).comp (tendsto_olverZeta (χ := χ) hc)
  have hJ' := (continuous_besselJ0'.tendsto 0).comp (tendsto_olverZeta (χ := χ) hc)
  rw [besselJ0_zero] at hJ
  rw [besselJ0'_zero] at hJ'
  have hlim := (((tendsto_olverAmp' hc hχ0 hχc).mul hJ).div (tendsto_freqS (χ := χ) hc) hσ.ne').add
    ((tendsto_olverAmp hc hχ0 hχc).mul hJ')
  simp only [zero_mul, zero_div, mul_zero, add_zero, Pi.div_apply, Function.comp_apply] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hp := pS_pos hc hs
  have hf := freqS_pos (s := s) hc hχc
  rw [← pS_mul_freqS hc hs hχc]
  unfold approxFlux olverAmp
  field_simp

/-- **The initial error energy vanishes at the edge.** -/
theorem tendsto_edge_energy {ψ u : ℝ → ℝ} {c χ c₀ C : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2)
    (hψ : Tendsto (fun s => ψ (xiOf c s)) (𝓝[>] 0) (𝓝 c₀))
    (hu : ∀ᶠ s in 𝓝[>] 0, |u (xiOf c s)| ≤ C * s ^ 2) :
    Tendsto (fun s => √((ψ (xiOf c s) - c₀ * approx c χ s) ^ 2
      + (u (xiOf c s) - c₀ * approxFlux c χ s) ^ 2 / aP c χ (xiOf c s) ^ 2)) (𝓝[>] 0) (𝓝 0) := by
  have hσ : 0 < √(c ^ 2 - χ) / c := div_pos (Real.sqrt_pos.mpr (by linarith)) hc
  -- the flux of the rung over `a`
  have hua : Tendsto (fun s => u (xiOf c s) / aP c χ (xiOf c s)) (𝓝[>] 0) (𝓝 0) := by
    have hK : Tendsto (fun s : ℝ => C / (√(c ^ 2 - χ) / c) * s) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun s : ℝ => C / (√(c ^ 2 - χ) / c) * s) (𝓝 0) (𝓝 (C / (√(c ^ 2 - χ) / c) * 0)) :=
        tendsto_const_nhds.mul tendsto_id
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ hK
    filter_upwards [self_mem_nhdsWithin, hu] with s hs hus
    have hs' : 0 < s := hs
    have hsq : 0 < √(c ^ 2 - χ) := Real.sqrt_pos.mpr (by linarith)
    have hp := pS_pos hc hs
    have hf := freqS_pos (s := s) hc hχc
    have hsP : s ≤ pS c s := by
      rw [pS_eq c s hc.ne']
      have : 0 ≤ s * (s ^ 2 / (4 * c ^ 2)) := by positivity
      linarith [show s * (1 + s ^ 2 / (4 * c ^ 2)) = s + s * (s ^ 2 / (4 * c ^ 2)) by ring]
    have hσf := sigma_le_freqS (s := s) hc hχ0 hχc
    rw [Real.norm_eq_abs, ← pS_mul_freqS hc hs hχc, abs_div, abs_of_pos (mul_pos hp hf),
      div_le_iff₀ (mul_pos hp hf)]
    have hC : 0 ≤ C * s ^ 2 := le_trans (abs_nonneg _) hus
    have hC0 : 0 ≤ C := by
      by_contra h; push Not at h; have : C * s ^ 2 < 0 := mul_neg_of_neg_of_pos h (by positivity); linarith
    calc |u (xiOf c s)| ≤ C * s ^ 2 := hus
      _ = C / (√(c ^ 2 - χ) / c) * s * (s * (√(c ^ 2 - χ) / c)) := by field_simp
      _ ≤ C / (√(c ^ 2 - χ) / c) * s * (pS c s * freqS c χ s) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hsP hσf hσ.le hp.le) (mul_nonneg (div_nonneg hC0 hσ.le) hs'.le)
  have he : Tendsto (fun s => ψ (xiOf c s) - c₀ * approx c χ s) (𝓝[>] 0) (𝓝 0) := by
    have := hψ.sub ((tendsto_approx hc hχ0 hχc).const_mul c₀)
    simpa using this
  have hv : Tendsto (fun s => u (xiOf c s) / aP c χ (xiOf c s) - c₀ * (approxFlux c χ s / aP c χ (xiOf c s)))
      (𝓝[>] 0) (𝓝 0) := by
    have := hua.sub ((tendsto_approxFlux_div hc hχ0 hχc).const_mul c₀)
    simpa using this
  have hlim := ((he.pow 2).add (hv.pow 2)).sqrt
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, Real.sqrt_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have ha : aP c χ (xiOf c s) ≠ 0 := by
    rw [← pS_mul_freqS hc hs hχc]; exact (mul_pos (pS_pos hc hs) (freqS_pos hc hχc)).ne'
  congr 2
  field_simp

end Cvs.Prolate.LiouvilleGreen.OlverInitialErrorZero

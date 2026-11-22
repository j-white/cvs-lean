import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable
import Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge
import Cvs.Prolate.LiouvilleGreen.LayerProlateSystem
import Cvs.Prolate.LiouvilleGreen.LayerPruferRate
import Cvs.Prolate.LiouvilleGreen.OlverAmplitudeAtEdge
import Cvs.Prolate.LiouvilleGreen.OlverLayerPhase
import Cvs.Prolate.LiouvilleGreen.OlverPhaseBracket

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The amplitude ratio is flat at the edge

`R = ζ/(P̃f_s)` has derivative `R′ = (f_s·a − ζa′)/a²`, `a = P̃f_s`, `a′ = P̃′f_s + P̃f_s′`, `P̃′ = 1 + 3s²/(4c²)`.
The brackets of Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge–Cvs.Prolate.LiouvilleGreen.OlverPhaseBracket make the numerator `O(s³)` against `a² ≥ s²σ²`, giving the explicit
`|R′| ≤ (s/c²)(1 + 3/(2σ²))` for `s > 0`.
-/

namespace Cvs.Prolate.LiouvilleGreen.OlverAmplitudeFlat

open Real Set Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable Cvs.Prolate.LiouvilleGreen.LayerPruferRate Cvs.Prolate.LiouvilleGreen.OlverLayerPhase Cvs.Prolate.LiouvilleGreen.LayerProlateSystem Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge Cvs.Prolate.LiouvilleGreen.OlverPhaseBracket Cvs.Prolate.LiouvilleGreen.OlverAmplitudeAtEdge

/-- **The ratio-derivative inequality**, in the brackets' variables. -/
theorem abs_ratio_deriv_le {s c σ f fp ζ P Pp : ℝ} (hs : 0 < s) (hc : 0 < c) (hσ : 0 < σ) (hσf : σ ≤ f)
    (hfp0 : 0 ≤ fp) (hfp : fp ≤ s / (c ^ 2 * f)) (hζ0 : σ * s ≤ ζ) (hζ1 : ζ ≤ s * f)
    (hfσ : f - σ ≤ s ^ 2 / (c ^ 2 * (f + σ))) (hP : P = s * (1 + s ^ 2 / (4 * c ^ 2)))
    (hPp : Pp = 1 + 3 * s ^ 2 / (4 * c ^ 2)) :
    |(f * (P * f) - ζ * (Pp * f + P * fp)) / (P * f) ^ 2| ≤ s / c ^ 2 * (1 + 3 / (2 * σ ^ 2)) := by
  have hf : 0 < f := lt_of_lt_of_le hσ hσf
  have hc2 : 0 < c ^ 2 := by positivity
  have hsP : s ≤ P := by
    rw [hP]
    have : 0 ≤ s * (s ^ 2 / (4 * c ^ 2)) := by positivity
    linarith [show s * (1 + s ^ 2 / (4 * c ^ 2)) = s + s * (s ^ 2 / (4 * c ^ 2)) by ring]
  have hP0 : 0 < P := lt_of_lt_of_le hs hsP
  have hζ00 : 0 ≤ ζ := le_trans (by positivity) hζ0
  -- the numerator
  have hT : P * f - ζ * Pp = (s * f - ζ) + s ^ 2 / (4 * c ^ 2) * (s * f - 3 * ζ) := by rw [hP, hPp]; ring
  have hT1 : |P * f - ζ * Pp| ≤ s * (f - σ) + s ^ 3 * f / (2 * c ^ 2) := by
    rw [hT]
    have hsf : 0 ≤ s * f := by positivity
    have h1 : |s * f - 3 * ζ| ≤ 2 * (s * f) := by rw [abs_le]; constructor <;> linarith
    have hk : 0 ≤ s ^ 2 / (4 * c ^ 2) := by positivity
    calc |(s * f - ζ) + s ^ 2 / (4 * c ^ 2) * (s * f - 3 * ζ)|
        ≤ |s * f - ζ| + |s ^ 2 / (4 * c ^ 2) * (s * f - 3 * ζ)| := abs_add_le _ _
      _ = (s * f - ζ) + s ^ 2 / (4 * c ^ 2) * |s * f - 3 * ζ| := by
          rw [abs_mul, abs_of_nonneg hk, abs_of_nonneg (by linarith)]
      _ ≤ s * (f - σ) + s ^ 2 / (4 * c ^ 2) * (2 * (s * f)) := by
          gcongr; linarith [show s * (f - σ) = s * f - σ * s by ring]
      _ = s * (f - σ) + s ^ 3 * f / (2 * c ^ 2) := by ring
  have hZP : ζ * P * fp ≤ s ^ 2 * P / c ^ 2 := by
    have : ζ * fp ≤ (s * f) * (s / (c ^ 2 * f)) := mul_le_mul hζ1 hfp hfp0 (by positivity)
    have e : (s * f) * (s / (c ^ 2 * f)) = s ^ 2 / c ^ 2 := by field_simp
    rw [e] at this
    calc ζ * P * fp = (ζ * fp) * P := by ring
      _ ≤ s ^ 2 / c ^ 2 * P := mul_le_mul_of_nonneg_right this hP0.le
      _ = s ^ 2 * P / c ^ 2 := by ring
  have hN : |f * (P * f) - ζ * (Pp * f + P * fp)|
      ≤ f * (s * (f - σ) + s ^ 3 * f / (2 * c ^ 2)) + s ^ 2 * P / c ^ 2 := by
    have e : f * (P * f) - ζ * (Pp * f + P * fp) = f * (P * f - ζ * Pp) - ζ * P * fp := by ring
    rw [e]
    calc |f * (P * f - ζ * Pp) - ζ * P * fp| ≤ |f * (P * f - ζ * Pp)| + |ζ * P * fp| := abs_sub _ _
      _ = f * |P * f - ζ * Pp| + ζ * P * fp := by
          rw [abs_mul f, abs_of_pos hf, abs_of_nonneg (show 0 ≤ ζ * P * fp by positivity)]
      _ ≤ f * (s * (f - σ) + s ^ 3 * f / (2 * c ^ 2)) + s ^ 2 * P / c ^ 2 := by
          gcongr
  -- against the denominator
  have hPf : 0 < (P * f) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hPf, div_le_iff₀ hPf]
  refine hN.trans ?_
  have hff : 2 * σ ^ 2 ≤ f * (f + σ) := by
    have h1 := mul_le_mul hσf hσf hσ.le hf.le
    have h2 := mul_le_mul_of_nonneg_right hσf hσ.le
    linarith [show f * (f + σ) = f * f + f * σ by ring, show 2 * σ ^ 2 = σ * σ + σ * σ by ring]
  have hsP2 : s ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ hs.le hsP 2
  -- three pieces
  have A1 : f * (s * (f - σ)) ≤ s / c ^ 2 * (1 / (2 * σ ^ 2)) * (P * f) ^ 2 := by
    have h1 : f * (s * (f - σ)) ≤ f * (s * (s ^ 2 / (c ^ 2 * (f + σ)))) := by gcongr
    refine h1.trans ?_
    rw [show f * (s * (s ^ 2 / (c ^ 2 * (f + σ)))) = s * s ^ 2 * f / (c ^ 2 * (f + σ)) by ring,
      show s / c ^ 2 * (1 / (2 * σ ^ 2)) * (P * f) ^ 2 = s * (P ^ 2 * f ^ 2) / (c ^ 2 * (2 * σ ^ 2)) by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : s ^ 2 * f * (2 * σ ^ 2) ≤ P ^ 2 * f ^ 2 * (f + σ) := by
      have := mul_le_mul hsP2 (mul_le_mul_of_nonneg_left hff hf.le) (by positivity) (by positivity)
      calc s ^ 2 * f * (2 * σ ^ 2) = s ^ 2 * (f * (2 * σ ^ 2)) := by ring
        _ ≤ P ^ 2 * (f * (f * (f + σ))) := this
        _ = P ^ 2 * f ^ 2 * (f + σ) := by ring
    have hs' : 0 ≤ s * c ^ 2 := by positivity
    calc s * s ^ 2 * f * (c ^ 2 * (2 * σ ^ 2)) = s * c ^ 2 * (s ^ 2 * f * (2 * σ ^ 2)) := by ring
      _ ≤ s * c ^ 2 * (P ^ 2 * f ^ 2 * (f + σ)) := mul_le_mul_of_nonneg_left h3 hs'
      _ = s * (P ^ 2 * f ^ 2) * (c ^ 2 * (f + σ)) := by ring
  have A2 : f * (s ^ 3 * f / (2 * c ^ 2)) ≤ s / c ^ 2 * (1 / 2) * (P * f) ^ 2 := by
    rw [show f * (s ^ 3 * f / (2 * c ^ 2)) = s * (s ^ 2 * f ^ 2) / (2 * c ^ 2) by ring,
      show s / c ^ 2 * (1 / 2) * (P * f) ^ 2 = s * (P ^ 2 * f ^ 2) / (2 * c ^ 2) by ring]
    gcongr
  have A3 : s ^ 2 * P / c ^ 2 ≤ s / c ^ 2 * (1 / σ ^ 2) * (P * f) ^ 2 := by
    rw [show s ^ 2 * P / c ^ 2 = s * (s * P) / c ^ 2 by ring,
      show s / c ^ 2 * (1 / σ ^ 2) * (P * f) ^ 2 = s * (P ^ 2 * f ^ 2 / σ ^ 2) / c ^ 2 by ring]
    gcongr
    rw [le_div_iff₀ (by positivity)]
    have hσ2 : σ ^ 2 ≤ f ^ 2 := pow_le_pow_left₀ hσ.le hσf 2
    have := mul_le_mul hsP (mul_le_mul_of_nonneg_left hσ2 hP0.le) (by positivity) hP0.le
    calc s * P * σ ^ 2 = s * (P * σ ^ 2) := by ring
      _ ≤ P * (P * f ^ 2) := this
      _ = P ^ 2 * f ^ 2 := by ring
  have e : s / c ^ 2 * (1 + 3 / (2 * σ ^ 2)) * (P * f) ^ 2
      = s / c ^ 2 * (1 / (2 * σ ^ 2)) * (P * f) ^ 2 + s / c ^ 2 * (1 / 2) * (P * f) ^ 2
        + s / c ^ 2 * (1 / σ ^ 2) * (P * f) ^ 2 + s / c ^ 2 * (1 / 2) * (P * f) ^ 2 := by
    field_simp; ring
  have hlast : 0 ≤ s / c ^ 2 * (1 / 2) * (P * f) ^ 2 := by positivity
  rw [e, mul_add]
  linarith

theorem hasDerivAt_pS {c : ℝ} (hc : 0 < c) (s : ℝ) : HasDerivAt (pS c) (1 + 3 * s ^ 2 / (4 * c ^ 2)) s := by
  have h : pS c = fun t => t + t ^ 3 / (4 * c ^ 2) := by
    funext t; rw [pS_eq c t hc.ne']; ring
  rw [h]
  refine ((hasDerivAt_id s).add ((hasDerivAt_pow 3 s).div_const _)).congr_deriv ?_
  simp

/-- The derivative of the amplitude ratio. -/
noncomputable def ampRatio' (c χ s : ℝ) : ℝ :=
  (freqS c χ s * (pS c s * freqS c χ s) - olverZeta c χ s * ((1 + 3 * s ^ 2 / (4 * c ^ 2)) * freqS c χ s
    + pS c s * (s * radXi c χ (xiOf c s) / (2 * c ^ 4 * freqS c χ s)))) / (pS c s * freqS c χ s) ^ 2

theorem hasDerivAt_ampRatio {c χ s : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (hs : 0 < s) :
    HasDerivAt (ampRatio c χ) (ampRatio' c χ s) s := by
  have ha := (hasDerivAt_pS hc s).mul (hasDerivAt_freqS hc hχc s)
  have hne : pS c s * freqS c χ s ≠ 0 := (mul_pos (pS_pos hc hs) (freqS_pos hc hχc)).ne'
  exact (hasDerivAt_olverZeta hc s).div ha hne

/-- **`|R′| ≤ (s/c²)(1 + 3/(2σ²))`** for `s > 0`. -/
theorem abs_ampRatio'_le {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hs : 0 < s) :
    |ampRatio' c χ s| ≤ s / c ^ 2 * (1 + 3 / (2 * (√(c ^ 2 - χ) / c) ^ 2)) := by
  have hσ : 0 < √(c ^ 2 - χ) / c := div_pos (Real.sqrt_pos.mpr (by linarith)) hc
  have hb := freqS_deriv_bounds hc hχ0 hχc hs.le
  have hfp : s * radXi c χ (xiOf c s) / (2 * c ^ 4 * freqS c χ s) ≤ s / (c ^ 2 * freqS c χ s) := hb.2
  exact abs_ratio_deriv_le hs hc hσ (sigma_le_freqS hc hχ0 hχc) hb.1 hfp
    (by linarith [sigma_mul_le_olverZeta hc hχ0 hχc hs.le, show √(c ^ 2 - χ) / c * s = s * (√(c ^ 2 - χ) / c) by ring])
    (olverZeta_le hc hχ0 hχc hs.le) (freqS_sub_sigma_le hc hχ0 hχc) (pS_eq c s hc.ne') rfl

end Cvs.Prolate.LiouvilleGreen.OlverAmplitudeFlat

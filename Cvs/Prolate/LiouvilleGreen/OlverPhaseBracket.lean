import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable
import Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge
import Cvs.Prolate.LiouvilleGreen.LayerPruferRate
import Cvs.Prolate.LiouvilleGreen.OlverLayerPhase

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Olver's phase is bracketed to third order at the edge

The layer frequency `f_s` is monotone on `s ≥ 0` (Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge), so `σs ≤ ζ(s) ≤ s·f_s(s)`, and
`s·f_s(s) − ζ(s) ≤ s(f_s(s) − σ) ≤ s³/(c²(f_s(s) + σ))`: near the edge Olver's phase is `s·f_s` to `O(s³)`.
-/

namespace Cvs.Prolate.LiouvilleGreen.OlverPhaseBracket

open Real Set intervalIntegral Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable Cvs.Prolate.LiouvilleGreen.LayerPruferRate Cvs.Prolate.LiouvilleGreen.OlverLayerPhase Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge

/-- **`f_s` is monotone on `s ≥ 0`.** -/
theorem monotoneOn_freqS {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    MonotoneOn (freqS c χ) (Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (continuous_freqS hc).continuousOn
    (fun s _ => (hasDerivAt_freqS hc hχc s).differentiableAt.differentiableWithinAt) fun s hs => ?_
  rw [interior_Ici] at hs
  rw [(hasDerivAt_freqS hc hχc s).deriv]
  exact (freqS_deriv_bounds hc hχ0 hχc (le_of_lt hs)).1

/-- **`ζ(s) ≤ s·f_s(s)`.** -/
theorem olverZeta_le {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hs : 0 ≤ s) :
    olverZeta c χ s ≤ s * freqS c χ s := by
  unfold olverZeta
  have h := intervalIntegral.integral_mono_on hs ((continuous_freqS hc).intervalIntegrable _ _)
    (intervalIntegrable_const (μ := MeasureTheory.volume) (c := freqS c χ s))
    fun u hu => monotoneOn_freqS hc hχ0 hχc hu.1 hs hu.2
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
  exact h

/-- **`f_s − σ ≤ s²/(c²(f_s + σ))`.** -/
theorem freqS_sub_sigma_le {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    freqS c χ s - √(c ^ 2 - χ) / c ≤ s ^ 2 / (c ^ 2 * (freqS c χ s + √(c ^ 2 - χ) / c)) := by
  have hf := freqS_pos (s := s) hc hχc
  have hσ0 : 0 ≤ √(c ^ 2 - χ) / c := div_nonneg (Real.sqrt_nonneg _) hc.le
  have hσ2 : (√(c ^ 2 - χ) / c) ^ 2 = (c ^ 2 - χ) / c ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by linarith)]
  have hb := (freqS_sq_sub_bounds (s := s) hc hχ0 hχc).2
  rw [← hσ2] at hb
  have hsum : 0 < freqS c χ s + √(c ^ 2 - χ) / c := by linarith
  rw [le_div_iff₀ (by positivity)]
  have e : (freqS c χ s - √(c ^ 2 - χ) / c) * (c ^ 2 * (freqS c χ s + √(c ^ 2 - χ) / c))
      = c ^ 2 * (freqS c χ s ^ 2 - (√(c ^ 2 - χ) / c) ^ 2) := by ring
  rw [e]
  have hc2 : 0 < c ^ 2 := by positivity
  calc c ^ 2 * (freqS c χ s ^ 2 - (√(c ^ 2 - χ) / c) ^ 2) ≤ c ^ 2 * (s ^ 2 / c ^ 2) :=
        mul_le_mul_of_nonneg_left hb hc2.le
    _ = s ^ 2 := by field_simp

end Cvs.Prolate.LiouvilleGreen.OlverPhaseBracket

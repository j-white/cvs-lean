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
import Cvs.Prolate.LiouvilleGreen.OlverLayerPhase
import Cvs.Prolate.LiouvilleGreen.OlverPhaseBracket
import Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# Olver's amplitude tends to one at the edge

With `P̃ = s(1 + s²/(4c²))` and `a = P̃f_s`, the amplitude ratio `R = ζ/a` satisfies
`σ/(f_s(1 + s²/(4c²))) ≤ R ≤ 1/(1 + s²/(4c²))` for `s > 0`, by `σs ≤ ζ ≤ s·f_s`; both bounds tend to one, so
`R → 1` and the amplitude `A = √R` tends to one as `s → 0⁺`.
-/

namespace Cvs.Prolate.LiouvilleGreen.OlverAmplitudeAtEdge

open Real Set Filter Topology Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable Cvs.Prolate.LiouvilleGreen.LayerPruferRate Cvs.Prolate.LiouvilleGreen.OlverLayerPhase Cvs.Prolate.LiouvilleGreen.LayerProlateSystem Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge Cvs.Prolate.LiouvilleGreen.OlverPhaseBracket

/-- Olver's amplitude ratio `R = ζ/(P̃f_s)`. -/
noncomputable def ampRatio (c χ s : ℝ) : ℝ := olverZeta c χ s / (pS c s * freqS c χ s)

theorem pS_eq (c s : ℝ) (hc : c ≠ 0) : pS c s = s * (1 + s ^ 2 / (4 * c ^ 2)) := by
  unfold pS xiOf; field_simp; ring

theorem freqS_zero {c χ : ℝ} (hc : 0 < c) : freqS c χ 0 = √(c ^ 2 - χ) / c := by
  unfold freqS qP xiOf
  congr 2
  ring

theorem ampRatio_le {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hs : 0 < s) :
    ampRatio c χ s ≤ 1 / (1 + s ^ 2 / (4 * c ^ 2)) := by
  have hf := freqS_pos (s := s) hc hχc
  have hk : 0 < 1 + s ^ 2 / (4 * c ^ 2) := by positivity
  unfold ampRatio
  rw [pS_eq c s hc.ne', div_le_div_iff₀ (by positivity) hk]
  have := olverZeta_le hc hχ0 hχc hs.le
  nlinarith

theorem le_ampRatio {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hs : 0 < s) :
    √(c ^ 2 - χ) / c / (freqS c χ s * (1 + s ^ 2 / (4 * c ^ 2))) ≤ ampRatio c χ s := by
  have hf := freqS_pos (s := s) hc hχc
  have hk : 0 < 1 + s ^ 2 / (4 * c ^ 2) := by positivity
  unfold ampRatio
  rw [pS_eq c s hc.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  have := sigma_mul_le_olverZeta hc hχ0 hχc hs.le
  have e : olverZeta c χ s * (freqS c χ s * (1 + s ^ 2 / (4 * c ^ 2)))
      = s * (1 + s ^ 2 / (4 * c ^ 2)) * freqS c χ s * (olverZeta c χ s / s) := by field_simp
  rw [e]
  have h2 : √(c ^ 2 - χ) / c ≤ olverZeta c χ s / s := by rw [le_div_iff₀ hs]; linarith
  have hp : 0 < s * (1 + s ^ 2 / (4 * c ^ 2)) * freqS c χ s := by positivity
  nlinarith

/-- **`R → 1` at the edge.** -/
theorem tendsto_ampRatio {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    Tendsto (ampRatio c χ) (𝓝[>] 0) (𝓝 1) := by
  have hσ : 0 < √(c ^ 2 - χ) / c := div_pos (Real.sqrt_pos.mpr (by linarith)) hc
  have hk : Continuous fun s : ℝ => 1 + s ^ 2 / (4 * c ^ 2) := by fun_prop
  have hlow : Tendsto (fun s => √(c ^ 2 - χ) / c / (freqS c χ s * (1 + s ^ 2 / (4 * c ^ 2)))) (𝓝[>] 0) (𝓝 1) := by
    have hcont : ContinuousAt (fun s => √(c ^ 2 - χ) / c / (freqS c χ s * (1 + s ^ 2 / (4 * c ^ 2)))) 0 := by
      have hne : freqS c χ 0 * (1 + (0 : ℝ) ^ 2 / (4 * c ^ 2)) ≠ 0 := by
        rw [freqS_zero hc]; simp; exact ⟨(Real.sqrt_pos.mpr (by linarith)).ne', hc.ne'⟩
      exact continuousAt_const.div ((continuous_freqS hc).continuousAt.mul hk.continuousAt) hne
    have h1 : √(c ^ 2 - χ) / c / (freqS c χ 0 * (1 + (0 : ℝ) ^ 2 / (4 * c ^ 2))) = 1 := by
      rw [freqS_zero hc]; simp; exact ⟨(Real.sqrt_pos.mpr (by linarith)).ne', hc.ne'⟩
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [h1] at this
  have hup : Tendsto (fun s : ℝ => 1 / (1 + s ^ 2 / (4 * c ^ 2))) (𝓝[>] 0) (𝓝 1) := by
    have hcont : ContinuousAt (fun s : ℝ => 1 / (1 + s ^ 2 / (4 * c ^ 2))) 0 :=
      continuousAt_const.div hk.continuousAt
        (show (1 : ℝ) + (0 : ℝ) ^ 2 / (4 * c ^ 2) ≠ 0 by simp)
    have h1 : (1 : ℝ) / (1 + (0 : ℝ) ^ 2 / (4 * c ^ 2)) = 1 := by simp
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    rwa [h1] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hup ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with s hs using le_ampRatio hc hχ0 hχc hs
  · filter_upwards [self_mem_nhdsWithin] with s hs using ampRatio_le hc hχ0 hχc hs

/-- **Olver's amplitude `A = √R` tends to one at the edge.** -/
theorem tendsto_olverAmp {c χ : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    Tendsto (fun s => √(ampRatio c χ s)) (𝓝[>] 0) (𝓝 1) := by
  have := (tendsto_ampRatio hc hχ0 hχc).sqrt
  simpa using this

end Cvs.Prolate.LiouvilleGreen.OlverAmplitudeAtEdge

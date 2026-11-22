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

/-
Copyright (c) 2026 Jesse White.
Released under Apache 2.0 license.

AI-assisted development: portions of this file were generated or
developed with the assistance of an AI system and subsequently reviewed
and verified by the author.
-/

/-!
# The second derivative of the layer frequency

`F_ξ = 2(c²ξ² + 2c²ξ + χ)/(ξ + 1)²` has `ξ`-derivative `4(c² − χ)/(ξ + 1)³`, so `f_s′ = s·F_ξ/(2c⁴f_s)` has
`f_s″ = (F_ξ + (s²/c²)·4(c² − χ)/(ξ + 1)³)/(2c⁴f_s) − s·F_ξ·f_s′/(2c⁴f_s²)`, exact and rational in `s`, `f_s`.
-/

namespace Cvs.Prolate.LiouvilleGreen.LayerFrequencySecondDerivative

open Real Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable Cvs.Prolate.LiouvilleGreen.LayerPruferRate Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge

/-- The layer frequency's derivative `f_s′`. -/
noncomputable def freqS' (c χ s : ℝ) : ℝ := s * radXi c χ (xiOf c s) / (2 * c ^ 4 * freqS c χ s)

/-- The layer frequency's second derivative `f_s″`. -/
noncomputable def freqS'' (c χ s : ℝ) : ℝ :=
  (radXi c χ (xiOf c s) + s ^ 2 / c ^ 2 * (4 * (c ^ 2 - χ) / (xiOf c s + 1) ^ 3)) / (2 * c ^ 4 * freqS c χ s)
    - s * radXi c χ (xiOf c s) * freqS' c χ s / (2 * c ^ 4 * freqS c χ s ^ 2)

theorem hasDerivAt_radXi {c χ ξ : ℝ} (hξ : ξ + 1 ≠ 0) :
    HasDerivAt (radXi c χ) (4 * (c ^ 2 - χ) / (ξ + 1) ^ 3) ξ := by
  have hN : HasDerivAt (fun x => 2 * (c ^ 2 * x ^ 2 + 2 * c ^ 2 * x + χ)) (2 * (c ^ 2 * (2 * ξ) + 2 * c ^ 2)) ξ := by
    have := ((((hasDerivAt_pow 2 ξ).const_mul (c ^ 2)).add ((hasDerivAt_id ξ).const_mul (2 * c ^ 2))).add_const χ).const_mul 2
    refine this.congr_deriv ?_; simp
  have hD : HasDerivAt (fun x => (x + 1) ^ 2) (2 * (ξ + 1)) ξ := by
    have := ((hasDerivAt_id ξ).add_const 1).pow 2
    refine this.congr_deriv ?_; simp
  have := hN.div hD (pow_ne_zero 2 hξ)
  refine this.congr_deriv ?_
  field_simp
  ring

theorem hasDerivAt_freqS' {c χ : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (s : ℝ) :
    HasDerivAt (freqS' c χ) (freqS'' c χ s) s := by
  have hξ1 : 0 < xiOf c s + 1 := by linarith [one_le_xiOf c s]
  have hf := freqS_pos (s := s) hc hχc
  have hR := (hasDerivAt_radXi (c := c) (χ := χ) hξ1.ne').comp s (hasDerivAt_xiOf c s hc.ne')
  have hnum := (hasDerivAt_id s).mul hR
  have hden := (hasDerivAt_freqS hc hχc s).const_mul (2 * c ^ 4)
  have := hnum.div hden (by positivity)
  refine this.congr_deriv ?_
  unfold freqS'' freqS'
  simp only [Pi.mul_apply, Function.comp_apply, id]
  field_simp

end Cvs.Prolate.LiouvilleGreen.LayerFrequencySecondDerivative

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
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
# The layer frequency near the edge

`f_s² = F/c²` with `F = 2q(ξ)/(ξ + 1)`, and `0 ≤ f_s² − σ² ≤ s²/c²`, `σ² = (c² − χ)/c²`. Its derivative is
`f_s′ = s·F_ξ/(2c⁴f_s)` with `F_ξ = 2(c²ξ² + 2c²ξ + χ)/(ξ + 1)² ≤ 2c²`, so `0 ≤ f_s′ ≤ s/(c²f_s)`: the frequency is
flat to second order at the edge.
-/

namespace Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge

open Real Cvs.Prolate.LiouvilleGreen.ProlateEnergyOutsideInterval Cvs.Prolate.LiouvilleGreen.EdgeLayerVariable Cvs.Prolate.LiouvilleGreen.LayerPruferRate

/-- The radicand `F = 2q(ξ)/(ξ + 1)`. -/
noncomputable def radS (c χ s : ℝ) : ℝ := 2 * qP c χ (xiOf c s) / (xiOf c s + 1)

/-- Its `ξ`-derivative `F_ξ = 2(c²ξ² + 2c²ξ + χ)/(ξ + 1)²`. -/
noncomputable def radXi (c χ ξ : ℝ) : ℝ := 2 * (c ^ 2 * ξ ^ 2 + 2 * c ^ 2 * ξ + χ) / (ξ + 1) ^ 2

theorem one_le_xiOf (c s : ℝ) : 1 ≤ xiOf c s := by
  unfold xiOf
  have : 0 ≤ s ^ 2 / (2 * c ^ 2) := by positivity
  linarith

theorem radS_pos {c χ s : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) : 0 < radS c χ s := by
  have hξ := one_le_xiOf c s
  unfold radS qP
  apply div_pos _ (by linarith)
  have h1 : 1 ≤ xiOf c s ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 (sq_nonneg c)]

theorem freqS_eq (c χ s : ℝ) : freqS c χ s = √(radS c χ s) / c := rfl

theorem freqS_sq {c χ s : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) : freqS c χ s ^ 2 = radS c χ s / c ^ 2 := by
  rw [freqS_eq, div_pow, Real.sq_sqrt (radS_pos hc hχc).le]

theorem freqS_pos {c χ s : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) : 0 < freqS c χ s :=
  div_pos (Real.sqrt_pos.mpr (radS_pos hc hχc)) hc

/-- **`0 ≤ f_s² − σ² ≤ s²/c²`.** -/
theorem freqS_sq_sub_bounds {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) :
    0 ≤ freqS c χ s ^ 2 - (c ^ 2 - χ) / c ^ 2 ∧ freqS c χ s ^ 2 - (c ^ 2 - χ) / c ^ 2 ≤ s ^ 2 / c ^ 2 := by
  rw [freqS_sq hc hχc]
  have hc2 : 0 < c ^ 2 := by positivity
  set ε := s ^ 2 / (2 * c ^ 2) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hs2 : s ^ 2 = 2 * c ^ 2 * ε := by rw [hε]; field_simp
  have hξ : xiOf c s = 1 + ε := rfl
  unfold radS qP
  rw [hξ, hs2]
  have h2 : 0 < 2 + ε := by linarith
  -- `F − (c² − χ) = ((3c² + χ)ε + 2c²ε²)/(2 + ε)`
  have key : 2 * (c ^ 2 * (1 + ε) ^ 2 - χ) / (1 + ε + 1) / c ^ 2 - (c ^ 2 - χ) / c ^ 2
      = ((3 * c ^ 2 + χ) * ε + 2 * c ^ 2 * ε ^ 2) / ((2 + ε) * c ^ 2) := by
    field_simp; ring
  rw [key]
  constructor
  · positivity
  · rw [div_le_div_iff₀ (by positivity) hc2]
    have : (3 * c ^ 2 + χ) * ε ≤ 4 * c ^ 2 * ε := by nlinarith
    nlinarith

/-- **The derivative of the layer frequency**: `f_s′ = s·F_ξ/(2c⁴f_s)`. -/
theorem hasDerivAt_freqS {c χ : ℝ} (hc : 0 < c) (hχc : χ < c ^ 2) (s : ℝ) :
    HasDerivAt (freqS c χ) (s * radXi c χ (xiOf c s) / (2 * c ^ 4 * freqS c χ s)) s := by
  have hξ := hasDerivAt_xiOf c s hc.ne'
  have hξ1 : 0 < xiOf c s + 1 := by linarith [one_le_xiOf c s]
  have hN : HasDerivAt (fun t => 2 * (c ^ 2 * xiOf c t ^ 2 - χ)) (2 * (c ^ 2 * (2 * xiOf c s * (s / c ^ 2)))) s :=
    (((hξ.pow 2).congr_deriv (by simp)).const_mul (c ^ 2) |>.sub_const χ).const_mul 2
  have hD : HasDerivAt (fun t => xiOf c t + 1) (s / c ^ 2) s := hξ.add_const 1
  have hF : HasDerivAt (radS c χ) (s / c ^ 2 * radXi c χ (xiOf c s)) s := by
    have := hN.div hD hξ1.ne'
    refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => rfl)).congr_deriv ?_
    unfold radXi
    field_simp
    ring
  have hsq := (hF.sqrt (radS_pos hc hχc).ne').div_const c
  have hfeq : (fun t => √(radS c χ t) / c) = freqS c χ := rfl
  rw [hfeq] at hsq
  refine hsq.congr_deriv ?_
  have hf : freqS c χ s * c = √(radS c χ s) := by rw [freqS_eq]; field_simp
  have hfp := freqS_pos (s := s) hc hχc
  rw [← hf]
  field_simp

theorem radXi_nonneg {c χ ξ : ℝ} (hχ0 : 0 ≤ χ) (hξ : 0 ≤ ξ) : 0 ≤ radXi c χ ξ := by
  unfold radXi; positivity

theorem radXi_le {c χ ξ : ℝ} (hχc : χ < c ^ 2) (hξ : 0 ≤ ξ) : radXi c χ ξ ≤ 2 * c ^ 2 := by
  unfold radXi
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg c]

/-- **`0 ≤ f_s′ ≤ s/(c²f_s)`** for `s ≥ 0`. -/
theorem freqS_deriv_bounds {c χ s : ℝ} (hc : 0 < c) (hχ0 : 0 ≤ χ) (hχc : χ < c ^ 2) (hs : 0 ≤ s) :
    0 ≤ s * radXi c χ (xiOf c s) / (2 * c ^ 4 * freqS c χ s)
      ∧ s * radXi c χ (xiOf c s) / (2 * c ^ 4 * freqS c χ s) ≤ s / (c ^ 2 * freqS c χ s) := by
  have hξ : 0 ≤ xiOf c s := by linarith [one_le_xiOf c s]
  have hf := freqS_pos (s := s) hc hχc
  have hR0 := radXi_nonneg (c := c) hχ0 hξ
  have hR1 := radXi_le (c := c) hχc hξ
  constructor
  · positivity
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : s * radXi c χ (xiOf c s) ≤ s * (2 * c ^ 2) := mul_le_mul_of_nonneg_left hR1 hs
    have hcf : 0 < c ^ 2 * freqS c χ s := by positivity
    nlinarith

end Cvs.Prolate.LiouvilleGreen.LayerFrequencyNearEdge
